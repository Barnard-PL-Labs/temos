// This file should probably not be in /src.
use crate::types::*;
use crate::predicate;
use crate::assumption;

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

fn to_sygus() {
    let updates = vec![Function(Add, Var("x".to_string()), Const(1)),
    Function(Sub, Var("x".to_string()), Const(1)),
    Signal(Var("x".to_string()))];

    let hoare = SygusHoareTriple {
        precond  : Bool(EQ, Var("x".to_string()), Const(0)),
        postcond : Bool(EQ, Var("x".to_string()), Const(1)),
        var_name: "x".to_string(),
        temporal: Next(1),
        updates: updates
    };

    println!("{}\n", hoare.to_sygus());
}

fn parse_sygus() {
    let function = String::from("(define-fun function ((x Int)) Int (+ (+ x 1) 2))");
    println!("{}", &function);
    let result = assumption::parse_syguslia_result(function);
    println!("{}", result);
}


pub fn examples() {
    to_smt2();
    println!("---------------------------------------");
    to_sygus();
    println!("---------------------------------------");
    parse_sygus();
    println!("---------------------------------------");
    to_assumption();
}
