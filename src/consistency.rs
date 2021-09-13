use crate::tsl::{Theory, PredicateLiteral};
use crate::theories::lia::Lia;

fn pair_preds<T: Theory>(preds: Vec<PredicateLiteral<T> >)
-> Vec<PredicateLiteral <T> > {
    let mut all_preds = preds.clone();
    let negs : Vec< PredicateLiteral<T> > = preds.iter().map(|p| p.negate()).collect();
    all_preds.extend(negs);
    let mut pair : Vec< PredicateLiteral<T> > = Vec::new();

    for i in 0..all_preds.len() {
        for j in i+1..all_preds.len() {
            pair.push(all_preds[i].and(&all_preds[j]));
        }
    }
    pair
}

/// Specifically bound to LIA due to limits of specialization.
/// RFC: https://rust-lang.github.io/rfcs/1210-impl-specialization.html
pub fn consistency_checking(preds: Vec< PredicateLiteral <Lia> >)
-> Vec<String> {
    let mut assumptions = Vec::new();
    for predicate in pair_preds(preds) {
        if predicate.is_unsat() {
            assumptions.push(predicate.to_tsl_assumption());
        }
    }
    assumptions
}
