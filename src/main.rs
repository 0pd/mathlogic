use std::{env, fs};

mod parser;
mod checker;

fn main() {
    let filename = env::args().nth(1).expect("Expected filename");
    let content = fs::read_to_string(&filename).expect("Could not read the file");
    for line in content.lines() {
        println!("{:?}", parser::parse(line));
    }
}
