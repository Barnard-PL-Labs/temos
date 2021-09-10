#![allow(dead_code)]
mod cvc4;
mod dto;
mod json;
mod lia;
mod tsl;
mod tsl_lia;
mod specification;
mod utils;
mod sample;

fn main() {
    let elevator = sample::elevator();
    let pred = &elevator.predicates[0];
    println!("{}", pred.to_tsl_assumption());
}
