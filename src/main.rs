#![allow(dead_code)]
mod cvc4;
mod dto;
mod json;
mod theories;
mod tsl;
mod specification;
mod consistency;
mod sample;

fn main() {
    let elevator = sample::elevator();
    let assumptions = consistency::consistency_checking(elevator.predicates);
    for assumption in assumptions {
        println!("{}", assumption);
    }
}
