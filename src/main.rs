#![allow(dead_code)]
mod types; 
mod parser;
mod hoare;
mod predicate;
mod utils;
mod examples;
use std::env;
use std::fs;

fn main() {
    let usage = "USAGE: ./temos <input.json> <input.tslmt>";
    let json_path = env::args().nth(1).expect(&usage);
    let tslmt_path = env::args().nth(2).expect(&usage);

    let lia_spec = parser::json::get_spec_from_json(&json_path);
    let assumptions = lia_spec.to_always_assume();

    let tslmt = fs::read_to_string(tslmt_path).unwrap();
    let final_tsl = [assumptions, tslmt].join("\n");
    println!("{}", final_tsl);
}
