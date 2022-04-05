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
        "--synth" => {
            let lia_spec = parser::json::get_spec_from_json(&json);
            let assumptions = lia_spec.to_always_assume();

            let tslmt = fs::read_to_string(tsl).unwrap();
            let final_tsl = [assumptions, tslmt].join("\n");
            println!("{}", final_tsl);
        }
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
