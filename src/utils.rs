use crate::tsl::{Theory, PredicateLiteral};
pub fn pair_preds<T: Theory>(preds: &Vec<PredicateLiteral<T> >)
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
