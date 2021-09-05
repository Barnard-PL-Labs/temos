use crate::tsl::{Pred, Funct, Temporal, FunctionLiteral, UpdateLiteral};
use std::rc::Rc;

/// Data Transformation Obligation.
/// Currently hardcoded for LIA.
pub struct Dto<F:Funct, P:Pred> {
    pub precond: Rc< FunctionLiteral<P> >,
    pub postcond: Rc< FunctionLiteral<P> >,
    pub temporal: Temporal,
    pub grammar: Vec < UpdateLiteral<F> >
}
