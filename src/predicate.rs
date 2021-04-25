pub use crate::types::*;
use std::collections::HashSet;

fn enumerate_preds(preds: Vec<Predicate>) -> HashSet<Predicate> {
    let mut all_preds = preds.clone();
    let negs : Vec<Predicate> = preds.iter().map(|p| p.neg()).collect();
    let mut powerset : HashSet<Predicate> = HashSet::new();

    all_preds.extend(negs);

    for i in 0..all_preds.len() {
        for j in i..all_preds.len() {
            powerset.insert(all_preds[i].and(&all_preds[j]));
        }
    }
    powerset
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils;

    #[test]
    fn test_predicates() {
        let preds = vec![Bool(LT, Var("x".to_string()), Const(5)),
                         Bool(EQ, Var("x".to_string()), Const(4)),
                         Bool(LT, Var("x".to_string()),
                                  Var("y".to_string()))];
        for predicate in &preds {
            assert_eq!(utils::run_cvc4(predicate.to_smt2(), "smt"), "sat\n");
        }
        for predicate in enumerate_preds(preds) {
            println!("\n{}\n", predicate.to_smt2());
        }
    }
}
