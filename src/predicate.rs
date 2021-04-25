pub use crate::types::*;

// TODO: ownership bonanaza
//fn enumerate_preds(preds: &Vec<Predicate>) -> Vec<Predicate> {
//    let mut all_preds = preds.clone();
//    let negs : Vec<Predicate> = preds.iter().map(|p| p.neg()).collect();
//    let mut powerset : Vec<Predicate> = Vec::new();
//
//    all_preds.extend(negs);
//
//    for i in 0..all_preds.len() {
//        for j in i..all_preds.len() {
//            powerset.push(all_preds[i].and(all_preds[j]));
//        }
//    }
//    powerset
//}

pub fn test_predicates() -> i32 {
    let preds = vec![Bool(LT, Var("x".to_string()), Const(5)),
                     Bool(EQ, Var("x".to_string()), Const(4)),
                     Bool(LT, Var("x".to_string()),
                              Var("y".to_string()))];
    for predicate in &preds {
        println!("\n{}\n", predicate.to_smt2());
    }
    0
}
