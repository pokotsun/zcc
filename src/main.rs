use std::env;
use std::iter::{Iterator, Peekable};
use std::process;
use std::slice::Iter;
use zcc::tokenize::*;

//
// Parser
//

enum BinOp {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Equal,  // ==
    NEqual, // !=
    Lt,     // <
    Le,     // <=
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

    // expr = equality
    fn expr(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        Node::equality(tok_peek)
    }

    // equality = relational ("==" relational | "!=" relational)
    fn equality(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::relational(tok_peek);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("==") {
                tok_peek.next();
                let rhs = Node::relational(tok_peek);
                node = Node::new_bin(BinOp::Equal, node, rhs);
                continue;
            }
            if tok.equal("!=") {
                tok_peek.next();
                let rhs = Node::relational(tok_peek);
                node = Node::new_bin(BinOp::NEqual, node, rhs);
                continue;
            }
            return node;
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::add(tok_peek);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("<") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Lt, node, rhs);
                continue;
            }

            if tok.equal("<=") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Le, node, rhs);
                continue;
            }
            if tok.equal(">") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Lt, rhs, node);
                continue;
            }
            if tok.equal(">=") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Le, rhs, node);
                continue;
            }
            return node;
        }
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::mul(tok_peek);
        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("+") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek);
                node = Node::new_bin(BinOp::Add, node, rhs);
                continue;
            }
            if tok.equal("-") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek);
                node = Node::new_bin(BinOp::Sub, node, rhs);
                continue;
            }
            return node;
        }
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::unary(tok_peek);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("*") {
                tok_peek.next();
                let rhs = Node::unary(tok_peek);
                node = Node::new_bin(BinOp::Mul, node, rhs);
                continue;
            }
            if tok.equal("/") {
                tok_peek.next();
                let rhs = Node::unary(tok_peek);
                node = Node::new_bin(BinOp::Div, node, rhs);
                continue;
            }
            return node;
        }
    }

    // unary = ("+" | "-") unary
    //       | primary
    fn unary(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("+") {
            tok_peek.next();
            return Node::unary(tok_peek);
        }

        if tok.equal("-") {
            tok_peek.next();
            return Node::new_bin(
                BinOp::Sub,
                Node::new(NodeKind::Num(0)),
                Node::unary(tok_peek),
            );
        }

        return Node::primary(tok_peek);
    }

    // primary = "(" expr ")" | num
    fn primary(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let tok = tok_peek.next().unwrap();
        if tok.equal("(") {
            let node = Node::expr(tok_peek);
            skip(tok_peek, ")");
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

fn gen_expr(node: Node, mut top: usize) -> usize {
    match node.kind {
        NodeKind::Num(val) => {
            println!("  mov ${}, {}", val, reg(top));
            top += 1;
        }
        NodeKind::Bin { op, lhs, rhs } => {
            top = gen_expr(*rhs, gen_expr(*lhs, top));
            let rd = reg(top - 2);
            let rs = reg(top - 1);
            top -= 1;

            match op {
                BinOp::Add => println!("  add {}, {}", rs, rd),
                BinOp::Sub => println!("  sub {}, {}", rs, rd),
                BinOp::Mul => println!("  imul {}, {}", rs, rd),
                BinOp::Div => {
                    println!("  mov {}, %rax", rd);
                    println!("  cqo");
                    println!("  idiv {}", rs);
                    println!("  mov %rax, {}", rd);
                }
                BinOp::Equal => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  sete %al");
                    println!("  movzb %al, {}", rd);
                }
                BinOp::NEqual => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  setne %al");
                    println!("  movzb %al, {}", rd);
                }
                BinOp::Lt => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  setl %al");
                    println!("  movzb %al, {}", rd);
                }
                BinOp::Le => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  setle %al");
                    println!("  movzb %al, {}", rd);
                }
            }
        }
    }
    top
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }

    // Tokenize and parse.
    let chars = args[1].clone();

    let tokens = tokenize(chars);
    let mut tok_iter = tokens.iter().peekable();

    let node = Node::expr(&mut tok_iter);

    let last_token = tok_iter.next().unwrap();
    if let TokenKind::Eof = last_token.kind {
    } else {
        error_tok(last_token, "extra token");
    }

    println!(".globl main");
    println!("main:");

    // Save callee-saved registers
    println!("  push %r12");
    println!("  push %r13");
    println!("  push %r14");
    println!("  push %r15");

    let top = gen_expr(node, 0);

    // Set the result of the expression to RAX so that
    // the result becomes a return value of this function.
    println!("  mov {}, %rax", reg(top - 1));

    println!("  pop %r15");
    println!("  pop %r14");
    println!("  pop %r13");
    println!("  pop %r12");

    println!("  ret");
}
