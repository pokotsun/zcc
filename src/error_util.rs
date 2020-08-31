use std::process;

pub fn error_at(loc: usize, line: &str, err_msg: &str) {
    eprintln!("{}", line);
    eprintln!("{}", " ".repeat(loc) + &format!("^ {}", err_msg));
    process::exit(1);
}
