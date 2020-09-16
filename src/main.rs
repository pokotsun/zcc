use std::env;
use std::iter::Iterator;
use std::process;
use zcc::codegen::*;
use zcc::parser::*;
use zcc::tokenize::*;

//
// Code Generator
//

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }

    // Tokenize and parse.
    let chars = args[1].clone();

    let tokens = tokenize(chars);
    let mut tok_iter = tokens.iter().peekable();

    let node = Node::expr(&mut tok_iter);

    let last_token = tok_iter.next().unwrap();
    if let TokenKind::Eof = last_token.kind {
    } else {
        error_tok(last_token, "extra token");
    }

    codegen(node);
}
