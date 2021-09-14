use crate::specification::Specification;
use crate::theories::lia::{Function, Predicate, Literal, Lia};
use crate::tsl::{Variable::Variable, FunctionLiteral, PredicateLiteral, UpdateLiteral, TheoryFunctions};

pub fn elevator() -> Specification<Lia> {
    let cells = vec![
        Variable(String::from("floor"))
    ];
    let assumptions = vec![
        // lte 1 floor
        PredicateLiteral::new(
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
            ]
        ),
        // lte floor 3
        PredicateLiteral::new(
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
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
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
            ]
        ),
        // lte floor 3
        PredicateLiteral::new(
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::LTE),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                        Literal::Const(3)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 1
        PredicateLiteral::new(
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                        Literal::Const(1)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 2
        PredicateLiteral::new(
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                        Literal::Const(2)
                    )),
                    vec![]
                )
            ]
        ),
        // eq floor 3
        PredicateLiteral::new(
            Lia::LIA,
            TheoryFunctions::Predicate(Predicate::EQ),
            vec![
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
                            Literal::Var(Variable(String::from("floor")))
                    )),
                    vec![]
                ),
                FunctionLiteral::new(
                    Lia::LIA,
                    TheoryFunctions::Function(Function::NullaryFunction(
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
                Lia::LIA,
                TheoryFunctions::Function(
                    Function::NullaryFunction(
                        Literal::Var(Variable(String::from("floor")))
                    )
                ),
                vec![]
            )
        }
    ];
    Specification::new(
        cells,
        assumptions,
        predicates,
        updates
    )
}
