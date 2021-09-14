#![allow(dead_code)]
mod cvc4;
mod dto;
mod json;
mod theories;
mod tsl;
mod specification;
mod utils;
mod consistency;
mod sample;

fn main() {
    // let elevator = sample::elevator();
    // let assumptions = consistency::consistency_checking(&(elevator.predicates));
    // for assumption in assumptions {
    //     println!("{}", assumption);
    // }
    let result = "(define-fun function ((x Int)) Int (+ (+ x 1) 2))";
    println!("{}", result);
    println!("{}", cvc4::parse_sygus_result(result));
}
