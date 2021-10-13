use crate::util::*;
use anyhow::Result;
use itertools::{multipeek, MultiPeek};
use std::rc::Rc;
use std::slice::Iter;
use std::{
    iter::{Enumerate, Iterator, Peekable},
    str::Chars,
};

// FIXME IdentのStringとwordは役割が被っていないか?
#[derive(Debug)]
pub enum TokenKind {
    Reserved,
    Ident(String), // Identifiers
    Num(i64),
    Str(Vec<String>), // String literal
}

#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind, // Token kind
    loc: usize,          // Token location
    line_no: usize,      // Line Number
    line: Rc<String>,    // Line which exists token
    pub word: String,    // Token word
}

impl Token {
    pub fn new(
        kind: TokenKind,
        loc: usize,
        line_no: usize,
        line: Rc<String>,
        word: String,
    ) -> Self {
        Token {
            kind,
            loc,
            line_no,
            line,
            word,
        }
    }

    pub fn equal(&self, s: &str) -> bool {
        self.word == s.to_string()
    }

    pub fn get_number(&self) -> Option<usize> {
        if let TokenKind::Num(val) = self.kind {
            return Some(val as usize);
        }
        None
    }

    pub fn get_ident(&self) -> Option<String> {
        if let TokenKind::Ident(_) = self.kind {
            return Some(self.word.clone());
        }
        None
    }
}

fn is_keyword(target: &str) -> bool {
    let keywords = [
        "return", "if", "else", "for", "while", "char", "int", "sizeof", "struct",
    ];
    keywords.iter().any(|keyword| target == *keyword)
}

pub fn is_typename(tok_peek: &mut Peekable<Iter<Token>>) -> bool {
    // REVIEW: このtype情報はどこかにまとめられないか
    let types = ["char", "int", "struct"];
    types.iter().any(|s| next_equal(tok_peek, s))
}

pub fn skip<'a>(tok_iter: &mut impl Iterator<Item = &'a Token>, s: &str) {
    let tok = tok_iter.next().unwrap();
    if !tok.equal(s) {
        error_tok(&tok, &format!("expected '{}', but got {}", s, tok.word));
    }
}

pub fn consume<'a>(tok_peek: &mut Peekable<Iter<Token>>, s: &str) -> bool {
    let is_equaled = next_equal(tok_peek, s);
    if is_equaled {
        tok_peek.next();
    }
    is_equaled
}

pub fn next_equal(tok_peek: &mut Peekable<Iter<Token>>, s: &str) -> bool {
    tok_peek.peek().filter(|tok| tok.equal(s)).is_some()
}

fn read_escaped_literal(chars_peek: &mut MultiPeek<Enumerate<Chars>>) -> String {
    let ch = chars_peek.next().map(|(_, ch)| ch).unwrap();
    match ch {
        '0'..='7' => {
            // Read an octal number
            let mut num = ch.to_digit(8).unwrap();
            for _ in 0..2 {
                // 3桁まで表せるため
                if let Some((_, ch @ '0'..='7')) = chars_peek.peek().cloned() {
                    chars_peek.next();
                    num <<= 3;
                    num += ch.to_digit(8).unwrap();
                }
            }
            num.to_string()
        }
        'x' => {
            // Read a hexadecimal number.
            if chars_peek
                .peek()
                .filter(|(_, ch)| ch.is_ascii_hexdigit())
                .is_some()
            {
                chars_peek.reset_peek();
                let mut num = 0;
                while let Some((_, ch)) = chars_peek
                    .peek()
                    .cloned()
                    .filter(|(_, ch)| ch.is_ascii_hexdigit())
                {
                    chars_peek.next();
                    num <<= 4;
                    num += ch.to_digit(16).unwrap();
                }
                num.to_string()
            } else {
                unimplemented!("invalid hex escape sequence");
            }
        }
        'a' | 'b' | 't' | 'n' | 'v' | 'f' | 'r' | 'e' => {
            // rust seem not to support ancient unicode escape literal.
            // so this code is very dirty.
            // please visit https://github.com/rust-lang/rust/issues/16744
            match ch {
                'a' => "7",
                'b' => "8",
                't' => "9",
                'n' => "10",
                'v' => "11",
                'f' => "12",
                'r' => "13",
                _ => "27", // e
            }
            .to_string()
        }
        _ => (ch as u32).to_string(),
    }
}

// TODO: ここにこれまでのtokenizeの全ての負債が詰まっている, 直すべし
fn read_string_literal(chars_peek: &mut MultiPeek<Enumerate<Chars>>) -> Vec<String> {
    let mut strings = Vec::new();
    loop {
        if let Some((_, ch)) = chars_peek.next() {
            match ch {
                '\"' => break,
                '\\' => {
                    strings.push(read_escaped_literal(chars_peek));
                }
                _ => {
                    strings.push((ch as u32).to_string());
                }
            }
        } else {
            unimplemented!("Missing end of string literal.");
        }
    }
    strings.push("0".to_string());
    strings
}

pub fn tokenize(line: String) -> Result<Vec<Token>> {
    let line = Rc::new(line);
    let mut chars_peek = multipeek(line.chars().enumerate());
    let mut tokens = Vec::new();
    let mut line_no: usize = 1;
    let mut pre_enter_loc: usize = 0;

    while let Some((loc, ch)) = chars_peek.peek().cloned() {
        chars_peek.reset_peek();

        if startswith(&mut chars_peek, "//") {
            // Singleline comment out
            while let Some((_, ch)) = chars_peek.next() {
                if ch == '\n' {
                    break;
                }
            }
            continue;
        } else if startswith(&mut chars_peek, "/*") {
            // Multiline comment out
            nth_next(&mut chars_peek, 2); // for /*
            while !startswith(&mut chars_peek, "*/") {
                if let None = chars_peek.next() {
                    break;
                }
            }
            nth_next(&mut chars_peek, 2); // for */
            continue;
        }
        chars_peek.peek();

        match ch {
            // skip whitespace characters.
            ' ' => {
                chars_peek.next();
            }
            '=' => {
                chars_peek.next();

                let token = match chars_peek.peek() {
                    Some((_, '=')) => {
                        chars_peek.next();
                        Token::new(
                            TokenKind::Reserved,
                            loc - pre_enter_loc,
                            line_no,
                            line.clone(),
                            "==".to_string(),
                        )
                    }
                    _ => {
                        chars_peek.reset_peek();
                        Token::new(
                            TokenKind::Reserved,
                            loc - pre_enter_loc,
                            line_no,
                            line.clone(),
                            "=".to_string(),
                        )
                    }
                };
                tokens.push(token);
            }
            '!' => {
                chars_peek.next();
                if let Some((_, '=')) = chars_peek.peek() {
                    chars_peek.next();
                    let token = Token::new(
                        TokenKind::Reserved,
                        loc - pre_enter_loc,
                        line_no,
                        line.clone(),
                        "!=".to_string(),
                    );
                    tokens.push(token);
                    continue;
                }
                error_at(loc, &line, "invalid token start with !.");
            }
            '<' => {
                chars_peek.next();
                let token = match chars_peek.peek() {
                    Some((_, '=')) => {
                        chars_peek.next();
                        Token::new(
                            TokenKind::Reserved,
                            loc - pre_enter_loc,
                            line_no,
                            line.clone(),
                            "<=".to_string(),
                        )
                    }
                    _ => {
                        chars_peek.reset_peek();
                        Token::new(
                            TokenKind::Reserved,
                            loc - pre_enter_loc,
                            line_no,
                            line.clone(),
                            "<".to_string(),
                        )
                    }
                };
                tokens.push(token);
            }
            '>' => {
                chars_peek.next();
                let token = match chars_peek.peek() {
                    Some((_, '=')) => {
                        chars_peek.next();
                        Token::new(
                            TokenKind::Reserved,
                            loc - pre_enter_loc,
                            line_no,
                            line.clone(),
                            ">=".to_string(),
                        )
                    }
                    _ => {
                        chars_peek.reset_peek();
                        Token::new(
                            TokenKind::Reserved,
                            loc - pre_enter_loc,
                            line_no,
                            line.clone(),
                            ">".to_string(),
                        )
                    }
                };
                tokens.push(token);
            }
            // TODO is_alnumに置き換える?
            'a'..='z' | 'A'..='Z' | '_' => {
                let mut ident = chars_peek
                    .next()
                    .and_then(|(_, c)| Some(c))
                    .unwrap()
                    .to_string();
                while let Some((_, c)) = chars_peek.peek().filter(|(_, c)| is_alnum(*c)) {
                    ident += &c.to_string();
                    chars_peek.next();
                }
                chars_peek.reset_peek();

                let kind = if is_keyword(&ident) {
                    TokenKind::Reserved
                } else {
                    TokenKind::Ident(ident.clone())
                };
                let token = Token::new(
                    kind,
                    loc - pre_enter_loc,
                    line_no,
                    line.clone(),
                    ident.clone(),
                );
                tokens.push(token);
            }
            '0'..='9' => {
                chars_peek.reset_peek();
                let num = strtol(&mut chars_peek);
                let token = Token::new(
                    TokenKind::Num(num),
                    loc - pre_enter_loc,
                    line_no,
                    line.clone(),
                    num.to_string(),
                );
                tokens.push(token);
            }
            // String literal
            '"' => {
                chars_peek.next();
                let strings = read_string_literal(&mut chars_peek);
                let word = strings.join("");
                let token = Token::new(
                    TokenKind::Str(strings),
                    loc - pre_enter_loc,
                    line_no,
                    line.clone(),
                    word,
                );
                tokens.push(token);
            }
            // Punctuator
            '+' | '-' | '*' | '/' | '(' | ')' | ',' | ';' | '{' | '}' | '[' | ']' | '&' | '.' => {
                chars_peek.next();
                let token = Token::new(
                    TokenKind::Reserved,
                    loc - pre_enter_loc,
                    line_no,
                    line.clone(),
                    ch.to_string(),
                );
                tokens.push(token);
            }
            '\n' => {
                pre_enter_loc = loc;
                line_no += 1;
                chars_peek.next();
            }
            _ => {
                return Err(error_at(loc, &line, &format!("invalid token: {}", ch)));
            }
        }
    }
    // eprintln!("{:#?}", tokens.iter().map(|x| x.word.clone()));
    Ok(tokens)
}

pub fn error_tok(tok: &Token, err_msg: &str) {
    error_at(tok.loc, &tok.line, err_msg);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn tokenize_0() {
        let code = "1;".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 2);
        assert_eq!(tokenized[0].word, "1");
        assert_eq!(tokenized[1].word, ";");
    }

    #[test]
    fn tokenize_add_sub() {
        let code = "1+2-32;".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 6);
        assert_eq!(tokenized[0].word, "1");
        assert_eq!(tokenized[1].word, "+");
        assert_eq!(tokenized[2].word, "2");
        assert_eq!(tokenized[3].word, "-");
        assert_eq!(tokenized[4].word, "32");
        assert_eq!(tokenized[5].word, ";");
    }

    #[test]
    fn tokenize_multiple_letter_variable() {
        let code = "abc = 3;".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[0].word, "abc");
        assert_eq!(tokenized[1].word, "=");
        assert_eq!(tokenized[2].word, "3");
    }

    #[test]
    fn tokenize_multiple_letter_with_num_variable() {
        let code = "abc123 = 3;".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[0].word, "abc123");
        assert_eq!(tokenized[1].word, "=");
        assert_eq!(tokenized[2].word, "3");
    }

    #[test]
    fn tokenize_if_else() {
        let code = "{ if (1) return 2; else return 3; }".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 13);
        assert_eq!(tokenized[1].word, "if");
        assert_eq!(tokenized[9].word, "return");
        assert_eq!(tokenized[10].word, "3");
    }

    #[test]
    fn tokenize_str() {
        let code = "{ \"abcdefg\"; }".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[1].word, "9798991001011021030");
        assert_eq!(tokenized[2].word, ";");
    }

    #[test]
    fn tokenize_escaped_literal() {
        let code = "{ \"\n\\e\\r\"; }".to_string();
        let tokenized = tokenize(code).unwrap();
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[1].word, "1027130");
        assert_eq!(tokenized[2].word, ";");
    }
}
