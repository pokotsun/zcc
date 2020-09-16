use crate::util::*;
use std::iter::Iterator;

pub enum TokenKind {
    Reserved,
    Num(i64),
    Eof,
}

pub struct Token {
    pub kind: TokenKind, // Token kind
    loc: usize,          // Token location
    line: String,        // Line which exists token
    word: String,        // Token word
}

impl Token {
    pub fn new(kind: TokenKind, loc: usize, line: String, word: String) -> Self {
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
}

pub fn skip<'a>(tok_iter: &mut impl Iterator<Item = &'a Token>, s: &str) {
    let tok = tok_iter.next().unwrap();
    if !tok.equal(s) {
        error_tok(&tok, &format!("expected '{}'", s));
    }
}

pub fn tokenize(line: String) -> Vec<Token> {
    let mut chars_peek = line.chars().enumerate().peekable();
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
                    _ => Token::new(TokenKind::Reserved, i, line.clone(), "=".to_string()),
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
                    _ => Token::new(TokenKind::Reserved, i, line.clone(), "<".to_string()),
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
                    _ => Token::new(TokenKind::Reserved, i, line.clone(), ">".to_string()),
                };
                tokens.push(token);
            }
            '0'..='9' => {
                let num = strtol(&mut chars_peek);
                let token = Token::new(TokenKind::Num(num), i, line.clone(), num.to_string());
                tokens.push(token);
            }
            // Punctuator
            '+' | '-' | '*' | '/' | '(' | ')' => {
                chars_peek.next();
                let token = Token::new(TokenKind::Reserved, i, line.clone(), ch.to_string());
                tokens.push(token);
            }
            _ => {
                error_at(i, &line, "invalid token");
            }
        }
    }
    let eof = Token::new(TokenKind::Eof, line.len(), line.clone(), "EOF".to_string());
    tokens.push(eof);
    tokens
}

pub fn error_tok(tok: &Token, err_msg: &str) {
    error_at(tok.loc, &tok.line, err_msg);
}