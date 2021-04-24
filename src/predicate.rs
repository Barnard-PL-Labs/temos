pub use crate::types::*;

/*
fn enumerate_preds(preds: &Vec<Predicate>) -> Vec<Predicate> {
    let negs : Vec<Predicate> = preds.iter().map(|p| p.neg()).collect();
    let all_preds : Vec<Predicate> = [preds, &negs].concat();
    let mut powerset : Vec<Predicate> = Vec::new();
    for i in 0..all_preds.len() {
        for j in i..all_preds.len() {
            powerset.push(all_preds[i].and(all_preds[j]));
        }
    }
    powerset
}
*/

pub fn test_predicates() {
    let preds = vec![Bool(LT, Var("x".to_string()), Const(5)),
                     Bool(EQ, Var("x".to_string()), Const(4)),
                     Bool(LT, Var("x".to_string()),
                              Var("y".to_string()))];
    for predicate in &preds {
        println!("\n{}\n", predicate.to_smt2());
    }
}
