use std::env;
use std::process;
use std::iter::Peekable;
use std::str::Chars;

fn strtol(chars: &mut Peekable<Chars>) -> i64 {
    let mut num = 0;
    while let Some(ch) = chars.peek() {
        match ch {
            '0'..='9' => {
                let x = chars.next().unwrap().to_digit(10).unwrap() as i64;
                num = num * 10 + x;
            }
            _ => break,
        }
    }
    num
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }

    let mut p = args[1].chars().peekable();

    let num = strtol(&mut p);

    // while let Some(current) = it.peek() {

    // }

    println!(".globl main");
    println!("main:");
    // println!("  mov ${}, %rax", );
    println!("  mov ${}, %rax", num);
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
}
