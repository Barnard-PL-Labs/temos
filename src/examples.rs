// This file should probably not be in /src.
use crate::types::*;
use crate::predicate;
use crate::sygus;
use crate::hoare;
use crate::utils;
use std::collections::HashSet;
use std::rc::Rc;
use std::fs;

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
        println!("SyGuS:\n{}\n----------------\n", &sygus);
        let result = utils::sygus_cvc4(sygus, "sygus", 1);
        let is_realizable = sygus::get_sygus_result(&result);
        println!("Command Line Option: --lang sygus --sygus-abort-size={}", temporal);
        println!("Result:\n{}\n---------------\n", &result);
        if is_realizable.is_some() {
            println!("Parse attempt:\n{}\n---------------\n",
                     is_realizable.unwrap());
        } else {
            println!("UNREALIZABLE\n---------------\n");
        }
    }
}

fn specification_test() {
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
    let spec = Specification {
        predicates : pred_vec,
        updates : update_vec
    };
    let fname = "assumptions.tsl";
    spec.write_assumption(&fname);
    println!("{}", fs::read_to_string(fname).unwrap());
    fs::remove_file(&fname).unwrap();
}

pub fn examples() {
    simple_bouncing_counter();
    println!("---------------------------------------");
    specification_test();
}
