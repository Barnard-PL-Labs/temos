#![allow(dead_code)]
mod cvc4;
mod dto;
mod json;
mod lia;
mod tsl;
mod specification;
mod utils;
mod sample;

fn main() {
    let elevator = sample::elevator();
    let preds = elevator.predicates;
    let pair = utils::pair_preds(preds);
    println!("{:?}", &pair);
    println!("{:?}", pair.len());
}
