use crate::util::*;
use itertools::multipeek;
use std::iter::{Iterator, Peekable};
use std::rc::Rc;
use std::slice::Iter;

// FIXME IdentのStringとwordは役割が被っていないか?
#[derive(Debug)]
pub enum TokenKind {
    Reserved,
    Ident(String), // Identifiers
    Num(i64),
    Eof,
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
    let keywords = ["return", "if", "else", "for", "while", "int"];
    keywords.iter().any(|keyword| target == *keyword)
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
            // Punctuator
            '+' | '-' | '*' | '/' | '(' | ')' | ',' | ';' | '{' | '}' | '&' => {
                chars_peek.next();
                let token = Token::new(TokenKind::Reserved, i, line.clone(), ch.to_string());
                tokens.push(token);
            }
            _ => error_at(i, &line, "invalid token"),
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

    #[test]
    fn tokenize_multiple_letter_variable() {
        let code = "abc = 3;".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 5);
        assert_eq!(tokenized[0].word, "abc");
        assert_eq!(tokenized[1].word, "=");
        assert_eq!(tokenized[2].word, "3");
    }

    #[test]
    fn tokenize_multiple_letter_with_num_variable() {
        let code = "abc123 = 3;".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 5);
        assert_eq!(tokenized[0].word, "abc123");
        assert_eq!(tokenized[1].word, "=");
        assert_eq!(tokenized[2].word, "3");
    }

    #[test]
    fn tokenize_if_else() {
        let code = "{ if (1) return 2; else return 3; }".to_string();
        let tokenized = tokenize(code);
        assert_eq!(tokenized.len(), 14);
        assert_eq!(tokenized[1].word, "if");
        assert_eq!(tokenized[9].word, "return");
        assert_eq!(tokenized[10].word, "3");
        assert_eq!(tokenized[13].word, "EOF");
    }
}
