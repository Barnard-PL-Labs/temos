#![allow(dead_code)]
mod types; 
mod parser;
mod hoare;
mod predicate;
mod utils;
mod examples;
use std::env;

fn main() {
    let usage = "USAGE: ./streamos <mode> <json> <tsl>";
    let mode = env::args().nth(1).expect(&usage);
    let json = env::args().nth(2).expect(&usage);
    let tsl = env::args().nth(3).expect(&usage);
    match &mode[..] {
        "--time" => {
            let (lia_dur, tsl_dur) = utils::time_all(&json, &tsl);
            println!("{}\n{}",
                     lia_dur.as_millis(),
                     tsl_dur.as_millis()); 
        },
        "--lia" => {
            let lia_spec = parser::json::get_spec_from_json(&json);
    let (ass, lia_dur) = utils::time_tsllia(lia_spec);
    println!("{}\n{}",
            ass,
            lia_dur.as_millis());
        }
        _ => panic!("")
    }
}
