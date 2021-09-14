use std::rc::Rc;
use crate::theories::lia::Lia;
use crate::tsl::{Temporal, FunctionLiteral, PredicateLiteral, UpdateLiteral, Theory};
use crate::cvc4;

/// Data Transformation Obligation.
/// Currently hardcoded for LIA.
pub struct Dto<T: Theory> {
    pub precond: Rc< PredicateLiteral<T> >,
    pub postcond: Rc< PredicateLiteral<T> >,
    pub temporal: Temporal,
    pub grammar: Vec< UpdateLiteral<T> >
}

impl Dto<Lia> {
    // TODO
    fn to_sygus(&self) -> String {
        panic!("Not Implemented Error")
    }
    fn synthesize_next(&self, timesteps: u32) -> FunctionLiteral<Lia> {
        let query = self.to_sygus();
        let result = cvc4::runner(&query, "sygus", timesteps);
        cvc4::parse_sygus_result(&result, &query)
    }
    // TODO
    fn synthesize_eventually(&self) -> FunctionLiteral<Lia> {
        panic!("Not Implemented Error")
    }
    pub fn synthesize(&self) -> FunctionLiteral<Lia> {
        match &self.temporal {
            Temporal::Next(num_next) => self.synthesize_next(num_next.clone()),
            Temporal::Eventually => self.synthesize_eventually()
        }
    }
}
