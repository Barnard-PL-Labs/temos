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
    let sample_query = String::from("
(set-logic LIA)
(synth-fun function ((x Int)) Int
    ((I Int))
    ((I Int ((+ x 1) (- x 1)
             (+ I 1) (- I 1)
             ))
    )
)

(constraint (forall ((x Int)) 
	(=> 
	(and (<= x 100) (> x 0))
	(and (<= (function x) 100) (>= (function x) 0))
	)))

(check-synth)
                                    ");
    println!("{}", cvc4::cvc4_runner(sample_query, "sygus", 0));
}
