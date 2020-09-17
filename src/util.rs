use itertools::structs::MultiPeek;
use std::iter::{Enumerate, Iterator};
use std::process;
use std::str::Chars;

#[macro_export]
macro_rules! matches(
    ($e:expr, $p:pat) => (
        match $e {
            $p => true,
            _ => false,
        }
    )
);

pub fn error(msg: &str) {
    eprintln!("{}", msg);
    process::exit(1);
}

pub fn error_at(loc: usize, line: &str, err_msg: &str) {
    eprintln!("{}", line);
    eprintln!("{}", " ".repeat(loc) + &format!("^ {}", err_msg));
    process::exit(1);
}

pub fn strtol(chars: &mut MultiPeek<Enumerate<Chars>>) -> i64 {
    let mut num = 0;
    while let Some((_, ch)) = chars.peek().filter(|(_, c)| c.is_digit(10)) {
        let x = ch.to_digit(10).unwrap() as i64;
        num = num * 10 + x;
        chars.next();
    }
    chars.reset_peek();
    num
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::multipeek;

    #[test]
    fn strtol_get_1() {
        let mut chars = multipeek("1".chars().enumerate());
        let actual = strtol(&mut chars);

        assert_eq!(1, actual);
        assert_eq!(None, chars.next())
    }

    #[test]
    fn strtol_get_12345() {
        let mut chars = multipeek("12345".chars().enumerate());
        let actual = strtol(&mut chars);

        assert_eq!(12345, actual);
        assert_eq!(None, chars.next())
    }

    #[test]
    fn strtol_get_none() {
        let mut chars = multipeek("".chars().enumerate());
        let actual = strtol(&mut chars);

        assert_eq!(0, actual);
        assert_eq!(None, chars.next())
    }
}
