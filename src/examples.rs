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

fn gen_hoare() {
    let pred_vec = vec![SpecPredicate{
        pred: Bool(EQ, Var(String::from("c")), Const(0)),
        temporal: vec![Next(0)]
    },
    SpecPredicate {
        pred: Bool(EQ, Var(String::from("c")), Const(1)),
        temporal: vec![Next(0)]
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
    }];
    let hoare_vec = hoare::enumerate_hoare(pred_vec, update_vec);
    for hoare in &hoare_vec {
        let sygus = hoare.to_sygus();
        println!("SyGuS:\n{}\n----------------\n", &sygus);
        println!("Result:\n{}\n---------------\n", utils::run_cvc4(sygus, "sygus"));
    }
}


pub fn examples() {
    to_smt2();
    println!("---------------------------------------");
    to_assumption();
    println!("---------------------------------------");
    parse_sygus();
    println!("---------------------------------------");
    gen_hoare();
}
