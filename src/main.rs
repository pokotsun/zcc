use std::env;
use std::iter::{Enumerate, Iterator, Peekable};
use std::process;
use std::str::Chars;

fn strtol(chars: &mut Peekable<Enumerate<Chars>>) -> i64 {
    let mut num = 0;
    while let Some((_, ch)) = chars.peek().filter(|(_, c)| c.is_digit(10)) {
        let x = ch.to_digit(10).unwrap() as i64;
        num = num * 10 + x;
        chars.next();
    }
    num
}

enum TokenKind {
    Reserved,
    Num(i64),
    Eof,
}

struct Token {
    kind: TokenKind, // Token kind
    loc: usize,      // Token location
    line: String,    // Line which exists token
    word: String,    // Token word
}

impl Token {
    fn new(kind: TokenKind, loc: usize, line: String, word: String) -> Self {
        Token {
            kind: kind,
            loc: loc,
            line: line,
            word: word,
        }
    }

    fn equal(&self, s: &str) -> bool {
        self.word == s.to_string()
    }

    fn get_number(&self) -> Option<i64> {
        if let TokenKind::Num(val) = self.kind {
            return Some(val);
        }
        None
    }
}

fn skip(tok_iter: &mut impl Iterator<Item = Token>, s: &str) {
    let tok = tok_iter.next().unwrap();
    if !tok.equal(s) {
        error_tok(&tok, &format!("expected '{}'", s));
    }
}

fn tokenize(line: String) -> Vec<Token> {
    let mut chars_peek = line.chars().enumerate().peekable();
    let mut tokens = Vec::new();

    while let Some((i, ch)) = chars_peek.peek().cloned() {
        match ch {
            // skip whitespace characters.
            ' ' => {
                chars_peek.next();
            }
            '0'..='9' => {
                let num = strtol(&mut chars_peek);
                let token = Token::new(
                    TokenKind::Num(num),
                    i.clone(),
                    line.clone(),
                    num.to_string(),
                );
                tokens.push(token);
            }
            // Punctuator
            '+' | '-' | '*' | '/' => {
                chars_peek.next();
                let token = Token::new(TokenKind::Reserved, i, line.clone(), ch.to_string());
                tokens.push(token);
            }
            _ => {
                error_at(i, &line, "invalid token");
            }
        }
    }
    let eof = Token::new(TokenKind::Eof, line.len(), line.clone(), "".to_string());
    tokens.push(eof);
    tokens
}

fn error_at(loc: usize, line: &str, err_msg: &str) {
    eprintln!("{}", line);
    eprintln!("{}", " ".repeat(loc) + &format!("^ {}", err_msg));
    process::exit(1);
}

fn error_tok(tok: &Token, err_msg: &str) {
    error_at(tok.loc, &tok.line, err_msg);
}

//
// Parser
//

enum BinOp {
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /
}

enum NodeKind {
    Num(i64), // Integer
    Bin {
        op: BinOp,
        lhs: Box<Node>, // Left-hand side
        rhs: Box<Node>, // Right-hand side
    },
}

// AST node type
struct Node {
    kind: NodeKind, // Node kind
}

impl Node {
    fn new(kind: NodeKind) -> Self {
        Self { kind: kind }
    }

    fn new_bin(op: BinOp, lhs: Node, rhs: Node) -> Self {
        let kind = NodeKind::Bin {
            op: op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
        Node::new(kind)
    }

    // expr = mul ("+" mul | "-" mul)*
    fn expr(mut tok_iter: &mut impl Iterator<Item = Token>) -> Node {
        let mut node = Node::mul(&mut tok_iter);

        loop {
            let tok = tok_iter.next().unwrap();
            if tok.equal("+") {
                let rhs = Node::mul(&mut tok_iter);
                node = Node::new_bin(BinOp::Add, node, rhs);
                continue;
            }
            if tok.equal("-") {
                let rhs = Node::mul(&mut tok_iter);
                node = Node::new_bin(BinOp::Sub, node, rhs);
                continue;
            }
            return node;
        }
    }

    // mul = primary ("*" primary | "/" primary)
    fn mul(mut tok_iter: &mut impl Iterator<Item = Token>) -> Node {
        let mut node = Node::primary(&mut tok_iter);

        loop {
            let tok = tok_iter.next().unwrap();
            if tok.equal("*") {
                let rhs = Node::primary(&mut tok_iter);
                node = Node::new_bin(BinOp::Mul, node, rhs);
                continue;
            }
            if tok.equal("/") {
                let rhs = Node::primary(&mut tok_iter);
                node = Node::new_bin(BinOp::Div, node, rhs);
                continue;
            }
            return node;
        }
    }

    // primary = "(" expr ")" | num
    fn primary(mut tok_iter: &mut impl Iterator<Item = Token>) -> Node {
        let tok = tok_iter.next().unwrap();
        if tok.equal("(") {
            let node = Node::expr(&mut tok_iter);
            skip(&mut tok_iter, ")");
            return node;
        }
        let node = Node::new(NodeKind::Num(tok.get_number().unwrap()));
        node
    }
}

//
// Code Generator
//

const REGISTERS: [&str; 6] = ["%r10", "%r11", "%r12", "%r13", "%r14", "%r15"];
fn reg(idx: usize) -> &'static str {
    REGISTERS
        .get(idx)
        .expect(&format!("register out of range: {}", idx))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }

    let chars = args[1].clone();

    let tokens = tokenize(chars);

    println!(".globl main");
    println!("main:");

    let mut iter = tokens.iter();

    let first_token = iter.next().unwrap();

    // The first token must be a number
    if let Some(val) = first_token.get_number() {
        println!("  mov ${}, %rax", val);
    } else {
        error_tok(first_token, "expected a number");
    }

    while let Some(token) = iter.next() {
        if token.equal("+") {
            let next_token = iter.next().unwrap();
            if let Some(val) = next_token.get_number() {
                println!("  add ${}, %rax", val);
            } else {
                error_tok(next_token, "expected a number");
            }
        }

        if token.equal("-") {
            let next_token = iter.next().unwrap();
            if let Some(val) = next_token.get_number() {
                println!("  sub ${}, %rax", val);
            } else {
                error_tok(next_token, "expected a number");
            }
        }
    }
    println!("  ret");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strtol_get_1() {
        let mut chars = "1".chars().enumerate().peekable();
        let actual = strtol(&mut chars);

        assert_eq!(1, actual);
        assert_eq!(None, chars.next())
    }

    #[test]
    fn strtol_get_12345() {
        let mut chars = "12345".chars().enumerate().peekable();
        let actual = strtol(&mut chars);

        assert_eq!(12345, actual);
        assert_eq!(None, chars.next())
    }

    #[test]
    fn strtol_get_none() {
        let mut chars = "".chars().enumerate().peekable();
        let actual = strtol(&mut chars);

        assert_eq!(0, actual);
        assert_eq!(None, chars.next())
    }
}
