use crate::tsl::{Pred, Funct, FunctionLiteral, UpdateLiteral, Variable};

/* 
 * FIMXE: can only handle assumptions that only have predicates.
 * I.e. 0 < i < 5 or i = 0 <-> j = 0 is okay,
 * but i = 0 -> [j <- j + 1] is not supported.
 */
pub struct Specification<F: Funct, P: Pred> {
    pub cells : Vec< Variable >,
    pub assumptions : Vec < FunctionLiteral<P> >,
    pub predicates : Vec< FunctionLiteral<P> >,
    pub updates : Vec< UpdateLiteral<F> >
}
