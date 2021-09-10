use crate::tsl::{Temporal, PredicateLiteral, UpdateLiteral, Theory};
use std::rc::Rc;

/// Data Transformation Obligation.
/// Currently hardcoded for LIA.
pub struct Dto<T: Theory> {
    pub precond: Rc< PredicateLiteral <T> >,
    pub postcond: Rc< PredicateLiteral <T> >,
    pub temporal: Temporal,
    pub grammar: Vec< UpdateLiteral <T> >
}
