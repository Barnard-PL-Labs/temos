#![allow(dead_code)]
mod cvc4;
mod dto;
mod json;
mod theories;
mod tsl;
mod specification;
mod utils;
mod sample;

fn main() {
    let elevator = sample::elevator();
    let pred = &elevator.predicates[0];
    println!("{}", pred.to_smt2_query());
}
