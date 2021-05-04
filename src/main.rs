#![allow(dead_code)]
mod types; 
mod parser;
mod hoare;
mod predicate;
mod tests;
mod utils;
mod examples;
use std::env;

fn main() {
    let usage = "USAGE: ./streamos <json> <tsl>";
    let json = env::args().nth(1).expect(&usage);
    let tsl = env::args().nth(2).expect(&usage);
    let (lia_dur, tsl_dur) = utils::time_all(&json, &tsl);
    println!("{}\n{}",
             lia_dur.as_millis(),
             tsl_dur.as_millis()); 
}
