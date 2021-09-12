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
    for pred in &elevator.predicates {
        println!("Query: ({})", pred);
        // let query : String = pred.to_smt2_query();
        // let result = cvc4::cvc4_runner(&query, "smt", 0);
        let result = pred.evaluate();
        println!("Result: {}", result);
    }
}
