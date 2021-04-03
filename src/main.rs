use anyhow::Result;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::iter::Iterator;
use std::process;
use zcc::codegen::*;
use zcc::parser::*;
use zcc::tokenize::*;

//
// Code Generator
//

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 && args.len() != 3 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }

    // Tokenize and parse.
    let read_symbol = args[1].clone();

    // By convention, read from stdin if a given filename is "-".
    let contents = match &*read_symbol {
        "-" => args[2].to_string(),
        _ => {
            let mut file = File::open(args[1].clone())?;
            let mut contents = String::new();
            file.read_to_string(&mut contents)?;
            contents
        }
    };

    let tokens = tokenize(contents)?;
    let tok_peek = tokens.iter().peekable();

    let prog = Parser::parse(tok_peek);

    codegen(prog)?;

    Ok(())
}
