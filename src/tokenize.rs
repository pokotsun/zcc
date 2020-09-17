use crate::util::*;
use itertools::multipeek;
use std::iter::Iterator;

#[derive(Debug)]
pub enum TokenKind {
    Reserved,
    Num(i64),
    Eof,
}

#[derive(Debug)]
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
        error_tok(&tok, &format!("expected '{}', but got {}", s, tok.word));
    }
}

pub fn tokenize(line: String) -> Vec<Token> {
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
            '0'..='9' => {
                chars_peek.reset_peek();
                let num = strtol(&mut chars_peek);
                let token = Token::new(TokenKind::Num(num), i, line.clone(), num.to_string());
                tokens.push(token);
            }
            // Punctuator
            '+' | '-' | '*' | '/' | '(' | ')' | ';' => {
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn tokenize_0() {
        let code = "1;".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 3);
        assert_eq!(tokenized[0].word, "1");
        assert_eq!(tokenized[1].word, ";");
    }

    #[test]
    fn tokenize_add_sub() {
        let code = "1+2-32;".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 7);
        assert_eq!(tokenized[0].word, "1");
        assert_eq!(tokenized[1].word, "+");
        assert_eq!(tokenized[2].word, "2");
        assert_eq!(tokenized[3].word, "-");
        assert_eq!(tokenized[4].word, "32");
        assert_eq!(tokenized[5].word, ";");
    }
}
