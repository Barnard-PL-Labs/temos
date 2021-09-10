use crate::tsl::PredicateLiteral;

fn pair_preds(preds: Vec<PredicateLiteral>) -> Vec<PredicateLiteral> {
    let mut all_preds = preds.clone();
    let negs : Vec<PredicateLiteral> = preds.iter().map(|p| p.negate()).collect();
    all_preds.extend(negs);
    let mut pair : Vec<PredicateLiteral> = Vec::new();

    for i in 0..all_preds.len() {
        for j in i+1..all_preds.len() {
            pair.push(all_preds[i].and(&all_preds[j]));
        }
    }
    pair
}

pub fn consistency_checking(preds: Vec<PredicateLiteral>) {
}

// pub fn gen_assumptions(preds: Vec<Predicate>) -> Vec<String> {
//     let mut assumptions = Vec::new();
//     for predicate in enumerate_preds(preds) {
//         if predicate.is_unsat() {
//             assumptions.push(predicate.to_assumption());
//         }
//     }
//     assumptions
// }
