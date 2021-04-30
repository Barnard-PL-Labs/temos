// This file should probably not be in /src.
use crate::types::*;
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
    }];
    let spec = Specification {
        predicates : pred_vec,
        updates : update_vec
    };
    println!("{}", spec.to_assumption());
    // If you want to write out to a file
    // let fname = "assumptions.tsl";
    // spec.write_assumption(&fname);
    // println!("{}", fs::read_to_string(fname).unwrap());
    // fs::remove_file(&fname).unwrap();
}

fn linux_cfs() {
    let pred_vec = vec![SpecPredicate{
        pred: Bool(LTE, Var(String::from("v1")), Var(String::from("v2"))),
        temporal: vec![Next(1)]
    },
    SpecPredicate {
        pred: Bool(LT, Var(String::from("v2")), Var(String::from("v1"))),
        temporal: vec![Next(1)]
    }];
    let update_vec = vec![Update {
        update_term: Function(Add, Var(String::from("v1")), Const(1)),
        var_name: String::from("v1"),
        depends: Vec::new()
    },
    Update {
        update_term: Function(Sub, Var(String::from("v2")), Const(1)),
        var_name: String::from("v2"),
        depends: Vec::new()
    }];
    let spec = Specification {
        predicates : pred_vec,
        updates : update_vec
    };
    println!("{}", spec.to_assumption());
}

fn dao() {
    let pred_vec = vec![SpecPredicate{
        pred: Bool(GTE, Var(String::from("balance")), Const(0)),
        temporal: vec![Next(1)]
    }];
    let update_vec = vec![Update {
        update_term: Function(Add, Var(String::from("balance")), Const(1)),
        var_name: String::from("balance"),
        depends: Vec::new()
    },
    Update {
        update_term: Signal(Var(String::from("balance"))),
        var_name: String::from("balance"),
        depends: Vec::new()
    },
    Update {
        update_term: Function(Sub, Var(String::from("balance")), Const(1)),
        var_name: String::from("balance"),
        depends: Vec::new()
    }];
    let spec = Specification {
        predicates : pred_vec,
        updates : update_vec
    };
    println!("{}", spec.to_assumption());
}

pub fn examples() {
    dao();
}
