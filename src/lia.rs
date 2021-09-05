use crate::tsl::{Funct, Pred, Variable};

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Literal {
    Var(Variable),
    Const(i32),
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Function {
    Literal(Literal),
    BinaryFunction(BinaryFunction)
}

impl Funct for Function {
    fn arity(self) -> u32 {
        match self {
            Function::Literal(_) => 0,
            Function::BinaryFunction(_) => 2
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum BinaryFunction {
    Add,
    Sub
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Predicate {
    LT,
    GT,
    EQ,
    LTE,
    GTE
}

impl Funct for Predicate {
    fn arity(self) -> u32 {2}
}

impl Pred for Predicate {
    fn evaluate(self) -> bool {
        panic!("Not Implemented Error")
    }
}

impl Predicate {
    fn to_string(&self) -> String {
        match self {
            Predicate::LT  => String::from("<"),
            Predicate::GT  => String::from(">"),
            Predicate::EQ  => String::from("="),
            Predicate::LTE => String::from("<="),
            Predicate::GTE => String::from(">=")
        }
    }
    fn to_tsl(&self) -> String {
        match self {
            Predicate::LT  => String::from("LT"),
            Predicate::GT  => String::from("GT"),
            Predicate::EQ  => String::from("EQ"),
            Predicate::LTE => String::from("LTE"),
            Predicate::GTE => String::from("GTE")
        }
    }
    fn reverse(&self) -> Predicate {
        match self {
            Predicate::LT  => Predicate::GTE,
            Predicate::GT  => Predicate::LTE,
            Predicate::LTE => Predicate::GT,
            Predicate::GTE => Predicate::LT,
            Predicate::EQ  => panic!("No reversal for EQ")
        }
    }
    fn is_lt(&self) -> bool {
        match self {
            Predicate::LT  => true,
            Predicate::LTE => true,
            _   => false
        }
    }
    fn is_gt(&self) -> bool {
        match self {
            Predicate::GT  => true,
            Predicate::GTE => true,
            _   => false
        }
    }
    fn arity(&self) -> u32 {2}
    fn evaluate(&self) -> bool {true}
}
