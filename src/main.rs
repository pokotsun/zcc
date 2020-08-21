use std::env;
use std::iter::Peekable;
use std::process;
use std::str::Chars;

fn strtol(chars: &mut Peekable<Chars>) -> i64 {
    let mut num = 0;
    while let Some(ch) = chars.peek().filter(|c| c.is_digit(10)) {
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
    word: String,    // Token word
}

impl Token {
    fn new(kind: TokenKind, word: String) -> Self {
        Token {
            kind: kind,
            word: word,
        }
    }

    fn equal(&self, s: &str) -> bool {
        self.word == s.to_string()
    }

    fn get_number(&self) -> Option<i64> {
        match self.kind {
            TokenKind::Num(val) => Some(val),
            _ => None,
        }
    }
}

fn tokenize(mut chars: &mut Peekable<Chars>) -> Vec<Token> {
    let mut tokens = Vec::new();

    while let Some(ch) = chars.peek().cloned() {
        match ch {
            // skip whitespace characters.
            ' ' => {
                chars.next();
            }
            '0'..='9' => {
                let num = strtol(&mut chars);
                let token = Token::new(TokenKind::Num(num), num.to_string());
                tokens.push(token);
            }
            '+' | '-' => {
                chars.next();
                let token = Token::new(TokenKind::Reserved, ch.to_string());
                tokens.push(token);
            }
            _ => {
                error("invalid token");
            }
        }
    }
    let eof = Token::new(TokenKind::Eof, "".to_string());
    tokens.push(eof);
    tokens
}

fn error(msg: &str) {
    eprintln!("{}", msg);
    process::exit(1);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }

    let mut chars = args[1].chars().peekable();

    let tokens = tokenize(&mut chars);

    println!(".globl main");
    println!("main:");

    let mut iter = tokens.iter();

    let first_token = iter.next().unwrap();

    // the first token must be a number
    if let Some(val) = first_token.get_number() {
        println!("  mov ${}, %rax", val);
    } else {
        error("expected a number");
    }

    while let Some(token) = iter.next() {
        if token.equal("+") {
            let next = iter.next().unwrap();
            if let Some(val) = next.get_number() {
                println!("  add ${}, %rax", val);
            } else {
                error("expected a number");
            }
        }

        if token.equal("-") {
            let next = iter.next().unwrap();
            if let Some(val) = next.get_number() {
                println!("  sub ${}, %rax", val);
            } else {
                error("expected a number");
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
        let mut chars = "1".chars().peekable();
        let actual = strtol(&mut chars);

        assert_eq!(1, actual);
        assert_eq!(None, chars.next())
    }

    #[test]
    fn strtol_get_12345() {
        let mut chars = "12345".chars().peekable();
        let actual = strtol(&mut chars);

        assert_eq!(12345, actual);
        assert_eq!(None, chars.next())
    }

    #[test]
    fn strtol_get_none() {
        let mut chars = "".chars().peekable();
        let actual = strtol(&mut chars);

        assert_eq!(0, actual);
        assert_eq!(None, chars.next())
    }
}
