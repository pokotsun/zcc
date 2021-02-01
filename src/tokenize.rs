use crate::util::*;
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
    Str, // String literal
}

#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind, // Token kind
    loc: usize,          // Token location
    line: Rc<String>,    // Line which exists token
    pub word: String,    // Token word
}

impl Token {
    pub fn new(kind: TokenKind, loc: usize, line: Rc<String>, word: String) -> Self {
        Token {
            kind,
            loc,
            line,
            word,
        }
    }

    pub fn equal(&self, s: &str) -> bool {
        self.word == s.to_string()
    }

    pub fn get_number(&self) -> Option<i64> {
        if let TokenKind::Num(val) = self.kind {
            return Some(val);
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
        "return", "if", "else", "for", "while", "char", "int", "sizeof",
    ];
    keywords.iter().any(|keyword| target == *keyword)
}

pub fn is_typename(tok_peek: &mut Peekable<Iter<Token>>) -> bool {
    // REVIEW: このtype情報はどこかにまとめられないか
    let types = ["char", "int"];
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
    // rust seem not to support ancient unicode escape literal.
    // so this code is very dirty.
    // please visit https://github.com/rust-lang/rust/issues/16744
    let ch = chars_peek.next().map(|(_, ch)| ch).unwrap();
    match ch {
        'a' | 'b' | 't' | 'n' | 'v' | 'f' | 'r' | 'e' => {
            match ch {
                'a' => "\u{07}",
                'b' => "\u{08}",
                't' => "\u{09}",
                'n' => "\u{0A}",
                'v' => "\u{0B}",
                'f' => "\u{0C}",
                'r' => "\u{0D}", // r
                _ => "\u{1B}",   // e
            }
            .to_string()
        }
        _ => ch.to_string(),
    }
}

// TODO: ここにこれまでのtokenizeの全ての負債が詰まっている, 直すべし
fn read_string_literal(chars_peek: &mut MultiPeek<Enumerate<Chars>>) -> String {
    let mut str = String::new();
    loop {
        if let Some((_, ch)) = chars_peek.next() {
            match ch {
                '\"' => break,
                '\\' => {
                    str += &read_escaped_literal(chars_peek);
                }
                _ => {
                    str += &ch.to_string();
                }
            }
        } else {
            unimplemented!("Missing end of string literal.");
        }
    }
    str + "\0"
}

pub fn tokenize(line: String) -> Vec<Token> {
    let line = Rc::new(line);
    let mut chars_peek = multipeek(line.chars().enumerate());
    let mut tokens = Vec::new();

    while let Some((i, ch)) = chars_peek.peek().cloned() {
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
                        Token::new(TokenKind::Reserved, i, line.clone(), "==".to_string())
                    }
                    _ => {
                        chars_peek.reset_peek();
                        Token::new(TokenKind::Reserved, i, line.clone(), "=".to_string())
                    }
                };
                tokens.push(token);
            }
            '!' => {
                chars_peek.next();
                if let Some((_, '=')) = chars_peek.peek() {
                    chars_peek.next();
                    let token = Token::new(TokenKind::Reserved, i, line.clone(), "!=".to_string());
                    tokens.push(token);
                    continue;
                }
                error_at(i, &line, "invalid token start with !.");
            }
            '<' => {
                chars_peek.next();
                let token = match chars_peek.peek() {
                    Some((_, '=')) => {
                        chars_peek.next();
                        Token::new(TokenKind::Reserved, i, line.clone(), "<=".to_string())
                    }
                    _ => {
                        chars_peek.reset_peek();
                        Token::new(TokenKind::Reserved, i, line.clone(), "<".to_string())
                    }
                };
                tokens.push(token);
            }
            '>' => {
                chars_peek.next();
                let token = match chars_peek.peek() {
                    Some((_, '=')) => {
                        chars_peek.next();
                        Token::new(TokenKind::Reserved, i, line.clone(), ">=".to_string())
                    }
                    _ => {
                        chars_peek.reset_peek();
                        Token::new(TokenKind::Reserved, i, line.clone(), ">".to_string())
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
                let token = Token::new(kind, i, line.clone(), ident.clone());
                tokens.push(token);
            }
            '0'..='9' => {
                chars_peek.reset_peek();
                let num = strtol(&mut chars_peek);
                let token = Token::new(TokenKind::Num(num), i, line.clone(), num.to_string());
                tokens.push(token);
            }
            // String literal
            '"' => {
                chars_peek.next();
                let str = read_string_literal(&mut chars_peek);
                let token = Token::new(TokenKind::Str, i, line.clone(), str);
                tokens.push(token);
            }
            // Punctuator
            '+' | '-' | '*' | '/' | '(' | ')' | ',' | ';' | '{' | '}' | '[' | ']' | '&' => {
                chars_peek.next();
                let token = Token::new(TokenKind::Reserved, i, line.clone(), ch.to_string());
                tokens.push(token);
            }
            _ => error_at(i, &line, "invalid token"),
        }
    }
    tokens
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
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 2);
        assert_eq!(tokenized[0].word, "1");
        assert_eq!(tokenized[1].word, ";");
    }

    #[test]
    fn tokenize_add_sub() {
        let code = "1+2-32;".to_string();
        let tokenized = tokenize(code);
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
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[0].word, "abc");
        assert_eq!(tokenized[1].word, "=");
        assert_eq!(tokenized[2].word, "3");
    }

    #[test]
    fn tokenize_multiple_letter_with_num_variable() {
        let code = "abc123 = 3;".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[0].word, "abc123");
        assert_eq!(tokenized[1].word, "=");
        assert_eq!(tokenized[2].word, "3");
    }

    #[test]
    fn tokenize_if_else() {
        let code = "{ if (1) return 2; else return 3; }".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 13);
        assert_eq!(tokenized[1].word, "if");
        assert_eq!(tokenized[9].word, "return");
        assert_eq!(tokenized[10].word, "3");
    }

    #[test]
    fn tokenize_str() {
        let code = "{ \"abcdefg\"; }".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[1].word, "abcdefg\0");
        assert_eq!(tokenized[2].word, ";");
    }

    #[test]
    fn tokenize_escaped_literal() {
        let code = "{ \"\n\\e\\r\"; }".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 4);
        assert_eq!(tokenized[1].word, "\u{0A}\u{1B}\u{0D}\u{0}");
        assert_eq!(tokenized[2].word, ";");
    }
}
