use crate::tsl::PredicateLiteral;
use crate::theories::lia::Lia;
use crate::utils::pair_preds;

/// Specifically bound to LIA due to limits of specialization.
/// RFC: https://rust-lang.github.io/rfcs/1210-impl-specialization.html
pub fn consistency_checking(preds: &Vec< PredicateLiteral <Lia> >)
-> Vec<String> {
    let mut assumptions = Vec::new();
    for predicate in pair_preds(preds) {
        if predicate.is_unsat() {
            assumptions.push(predicate.to_tsl_assumption());
        }
    }
    assumptions
}
