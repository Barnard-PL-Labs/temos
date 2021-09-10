use crate::tsl::{PredicateLiteral, UpdateLiteral, Variable, Theory};

/* 
 * FIMXE: can only handle assumptions that only have predicates.
 * I.e. 0 < i < 5 or i = 0 <-> j = 0 is okay,
 * but i = 0 -> [j <- j + 1] is not supported.
 */
pub struct Specification<T: Theory> {
    pub cells : Vec<Variable>,
    pub assumptions : Vec < PredicateLiteral<T> >,
    pub predicates : Vec< PredicateLiteral<T> >,
    pub updates : Vec< UpdateLiteral<T> >
}
