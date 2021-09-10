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
    let _elevator = sample::elevator();
}
