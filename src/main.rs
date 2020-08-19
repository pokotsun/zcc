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
    kind: TokenKind,  // Token kind
    next: Box<Token>, // next token
    loc: usize,       // Token location
    word: String,     // Token word
}

impl Token {
    fn equal(&self, s: &str) -> bool {
        self.word == s.to_string()
    }
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

    println!(".globl main");
    println!("main:");
    println!("  mov ${}, %rax", strtol(&mut chars));
    while let Some(ch) = chars.peek().cloned() {
        match ch {
            '+' => {
                chars.next();
                println!("  add ${}, %rax", strtol(&mut chars));
            }
            '-' => {
                chars.next();
                println!("  sub ${}, %rax", strtol(&mut chars));
            }
            _ => {
                eprintln!("unexpected character: {}", ch);
                process::exit(1);
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
