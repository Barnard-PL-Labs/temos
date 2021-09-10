use crate::specification::Specification;
use crate::lia::{Function, Predicate, Literal, Lia};
use crate::tsl::{Variable::Variable, FunctionLiteral, PredicateLiteral, UpdateLiteral};
use std::rc::Rc;

pub fn elevator() -> Specification<Lia> {
    let cells = vec![
        Variable(String::from("floor"))
    ];
    let assumptions = vec![
        // lte 1 floor
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
            ]
        ),
        // lte floor 3
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(3)
                    )),
                    vec![]
                )
            ]
        )
    ];
    let predicates = vec![
        // lte 1 floor
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
            ]
        ),
        // lte floor 3
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(3)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 1
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 2
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(2)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 3
        PredicateLiteral::new(
            Lia::Lia,
            Rc::new(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::Lia,
                    Rc::new(Function::NullaryFunction(
                        Literal::Const(3)
                    )),
                    vec![]
                )
            ]
        ),
    ];
    let updates = vec![
        UpdateLiteral {
            sink: Variable(String::from("floor")),
            update: FunctionLiteral::new(
                Lia::Lia,
                Rc::new(
                    Function::NullaryFunction(
                        Literal::Var(Variable(String::from("floor")))
                    )
                ),
                vec![]
            )
        }
    ];
    Specification {
        cells,
        assumptions,
        predicates,
        updates
    }
}
