use std::collections::HashMap;
use std::rc::Rc;
use crate::tsl::{PredicateLiteral, UpdateLiteral};
use crate::tsl::{Variable, Theory, Temporal};
use crate::theories::lia::Lia;
use crate::dto::Dto;
use crate::utils::pair_preds;

/* 
 * FIMXE: can only handle assumptions that only have predicates.
 * I.e. 0 < i < 5 or i = 0 <-> j = 0 is okay,
 * but i = 0 -> [j <- j + 1] is not supported.
 */
pub struct Specification<T: Theory> {
    cells : Vec<Variable>,
    assumptions : Vec < PredicateLiteral<T> >,
    pub predicates : Vec< PredicateLiteral<T> >,
    updates_by_sink : HashMap< Variable, Vec< UpdateLiteral <T> > >
}

impl<T> Specification<T> where T: Theory {
    pub fn new(cells: Vec<Variable>,
               assumptions : Vec < PredicateLiteral<T> >,
               predicates : Vec< PredicateLiteral<T> >,
               updates : Vec< UpdateLiteral<T> >)
        -> Specification<T> {
            let mut updates_by_sink = HashMap::new();
            for update_literal in updates {
                let sink = update_literal.sink.clone();
                let function = update_literal.clone();
                let sink_vec = updates_by_sink.entry(sink).or_insert(vec![]);
                sink_vec.push(function);
            };
            Specification {
                cells,
                assumptions,
                predicates,
                updates_by_sink
            }
        }
}


// O(n^3) but it's probably fast enough.
impl Specification<Lia> {
    fn generate_dtos(&self) -> Vec< Dto<Lia> > {
        let mut dto_vec = Vec::new();
        // Let's get down to business,
        // to defeat, the borrow checker...
        let pred_pairs : Vec<_> = pair_preds(&self.predicates)
            .into_iter()
            .map(Rc::new)
            .collect();
        for i in 0..pred_pairs.len() {
            let precond = Rc::clone(&pred_pairs[i]);
            for j in i+1..pred_pairs.len() {
                let postcond = Rc::clone(&pred_pairs[j]);
                for var in postcond.get_vars() {
                    let grammar = self.updates_by_sink
                        .get(&var)
                        .expect(&format!("Sink {} not found!", var));
                    let dto = Dto {
                        precond: Rc::clone(&precond),
                        postcond: Rc::clone(&postcond),
                        temporal: Temporal::Next(1), // FIXME
                        grammar: grammar.clone()
                    };
                    dto_vec.push(dto);
                }
            }
        }
        dto_vec
    }
}
