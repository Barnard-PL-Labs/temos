// This file should probably not be in /src.
use crate::types::*;
use crate::predicate;
use crate::sygus;
use crate::hoare;
use crate::utils;
use std::collections::HashSet;
use std::rc::Rc;

fn to_smt2() {
    let predicate = Bool(LT, Var("x".to_string()), Const(5));
    println!("{}\n", predicate.to_smt2());
}

fn to_assumption() {
    let preds = vec![Bool(LT, Var("x".to_string()), Const(5)),
    Bool(EQ, Var("x".to_string()), Const(4)),
    Bool(LT, Var("x".to_string()),
    Var("y".to_string()))];
    for assumption in predicate::gen_assumptions(preds) {
        println!("{}", assumption);
    }
}

fn parse_sygus() {
    let function = String::from("(define-fun function ((x Int)) Int (+ (+ x 1) 2))");
    println!("{}", &function);
    let result = sygus::parse_syguslia_result(function);
    println!("{}", result);
}

fn simple_bouncing_counter() {
    let pred_vec = vec![SpecPredicate{
        pred: Bool(EQ, Var(String::from("c")), Const(0)),
        temporal: vec![Next(0)]
    },
    SpecPredicate {
        pred: Bool(EQ, Var(String::from("c")), Const(100)),
        temporal: vec![Next(0)]
    },
    SpecPredicate {
        pred: Predicate::new_and(
            Bool(LTE, Var(String::from("c")), Const(100)),
            Bool(LTE, Const(0), Var(String::from("c"))),
        ),
        temporal: vec![Next(1)]
    }];
    let update_vec = vec![Update {
        update_term: Function(Add, Var(String::from("c")), Const(1)),
        var_name: String::from("c"),
        depends: Vec::new()
    },
    Update {
        update_term: Function(Sub, Var(String::from("c")), Const(1)),
        var_name: String::from("c"),
        depends: Vec::new()
    },
    Update {
        update_term: Signal(Var(String::from("c"))),
        var_name: String::from("c"),
        depends: Vec::new()
    }];
    let hoare_vec = hoare::enumerate_hoare(pred_vec, update_vec);
    for hoare in &hoare_vec {
        let sygus = hoare.to_sygus();
        let temporal = match *hoare.temporal {
            Next(i) => i,
            _ => 0
        };
        println!("Command Line Option: --lang sygus --sygus-abort-size={}", temporal);
        println!("SyGuS:\n{}\n----------------\n", &sygus);
        println!("Result:\n{}\n---------------\n",
                 utils::sygus_cvc4(sygus, "sygus", 1));
    }
}

pub fn examples() {
    to_smt2();
    println!("---------------------------------------");
    to_assumption();
    println!("---------------------------------------");
    simple_bouncing_counter();
    println!("---------------------------------------");
    parse_sygus();
}