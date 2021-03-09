use crate::tokenize::Token;
use anyhow::anyhow;
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
pub struct LabelCounter {
    idx: usize,
}

impl LabelCounter {
    pub fn new() -> Self {
        LabelCounter { idx: 0 }
    }
}

impl Iterator for LabelCounter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let x = self.idx;
        self.idx += 1;
        Some(x)
    }
}

pub fn error(msg: &str) {
    eprintln!("{}", msg);
    process::exit(1);
}

pub fn error_at(loc: usize, line: &str, err_msg: &str) -> anyhow::Error {
    let msg = format!(
        "{}\n{}",
        line,
        " ".repeat(7 + loc) + &format!("^ {}", err_msg)
    );
    anyhow!(msg)
}

pub fn error_tok(tok: &Token, err_msg: &str) {
    eprintln!("{}", tok.word);
    error(err_msg);
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

pub fn startswith(chars: &mut MultiPeek<Enumerate<Chars>>, actual: &str) -> bool {
    let mut ok = true;
    for a in actual.chars() {
        if chars.peek().and_then(|x| Some(x.1)) != Some(a) {
            ok = false;
            break;
        }
    }
    chars.reset_peek();
    ok
}

pub fn nth_peek<'a>(
    chars: &'a mut MultiPeek<Enumerate<Chars>>,
    n: usize,
) -> Option<&'a (usize, char)> {
    for _ in 0..n - 1 {
        chars.peek();
    }
    chars.peek()
}

pub fn is_alpha(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

pub fn is_alnum(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
pub fn align_to(n: usize, align: usize) -> usize {
    (n + align - 1) / align * align
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

    #[test]
    fn startswith_return_ok() {
        let mut peeks = multipeek("return abc;".chars().enumerate());
        assert!(startswith(&mut peeks, "return"));
        assert_eq!(peeks.next(), Some((0, 'r')));
    }

    #[test]
    fn startswith_return_ng() {
        let mut peeks = multipeek("123; return abc;".chars().enumerate());
        assert!(!startswith(&mut peeks, "return"));
        assert_eq!(peeks.next(), Some((0, '1')));
    }
}
