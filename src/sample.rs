use crate::specification::Specification;
use crate::lia::{Function, Predicate};

fn elevator() -> Specification<Function,Predicate> {
    let cells = vec![];
    let assumptions = vec![];
    let predicates = vec![];
    let updates = vec![];
    Specification {
        cells,
        assumptions,
        predicates,
        updates
    }
}
