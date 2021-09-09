use crate::specification::Specification;
use crate::lia::{Function, Predicate, Literal};
use crate::tsl::{Variable::Variable, FunctionLiteral, UpdateLiteral};

pub fn elevator() -> Specification {
    let cells = vec![
        Variable(String::from("floor"))
    ];
    let assumptions = vec![
        // lte 1 floor
        FunctionLiteral::new(
            Box::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
            ]
        ),
        // lte floor 3
        FunctionLiteral::new(
            Box::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                        Literal::Const(3)
                    )),
                    vec![]
                )
            ]
        )
    ];
    let predicates = vec![
        // lte 1 floor
        FunctionLiteral::new(
            Box::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
            ]
        ),
        // lte floor 3
        FunctionLiteral::new(
            Box::new(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                        Literal::Const(3)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 1
        FunctionLiteral::new(
            Box::new(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 2
        FunctionLiteral::new(
            Box::new(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                        Literal::Const(2)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 3
        FunctionLiteral::new(
            Box::new(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Box::new(Function::NullaryFunction(
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
                Box::new(
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