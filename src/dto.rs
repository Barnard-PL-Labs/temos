use crate::tsl::{Temporal, FunctionLiteral, UpdateLiteral};
use std::rc::Rc;

/// Data Transformation Obligation.
/// Currently hardcoded for LIA.
pub struct Dto {
    pub precond: Rc<FunctionLiteral>,
    pub postcond: Rc<FunctionLiteral>,
    pub temporal: Temporal,
    pub grammar: Vec<UpdateLiteral>
}
