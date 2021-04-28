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

// FIXME: doesn't do what its name suggests...
pub fn enumerate_spec_preds(preds: Vec<SpecPredicate>) -> Vec<SpecPredicate> {
    let mut all_preds = preds.clone();
    for predicate in preds {
        let negated = SpecPredicate {
            pred: predicate.pred.neg(),
            temporal: predicate.temporal.clone()
        };
        all_preds.push(negated);
    }
    all_preds
}

pub fn gen_assumptions(preds: Vec<Predicate>) -> Vec<String> {
    let mut assumptions = Vec::new();
    for predicate in enumerate_preds(preds) {
        if predicate.is_unsat() {
            assumptions.push(predicate.to_assumption());
        }
    }
    assumptions
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
            assert_eq!(utils::cvc4_generic(predicate.to_smt2(), "smt"), "sat\n");
        }
        for predicate in enumerate_preds(preds) {
            println!("\n{}\n", predicate.to_smt2());
        }
    }
}
