use crate::tsl::{PredicateLiteral};

fn powerset_preds(preds: Vec<PredicateLiteral>) -> Vec<PredicateLiteral> {
    let mut all_preds = preds.clone();
    let negs : Vec<PredicateLiteral> = preds.iter().map(|p| p.negate()).collect();
    all_preds.extend(negs);
    let mut powerset : Vec<PredicateLiteral> = Vec::new();

    for i in 0..all_preds.len() {
        for j in i..all_preds.len() {
            powerset.push(all_preds[i].and(&all_preds[j]));
        }
    }
    powerset
}
