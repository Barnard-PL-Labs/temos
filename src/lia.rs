use crate::tsl::{Funct, Pred, Variable, Theory};
use std::fmt;
use std::fmt::Display;

#[derive(Debug, Clone, Copy)]
pub enum Lia {
    Lia
}
impl Theory for Lia {}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Literal {
    Var(Variable),
    Const(i32),
}

impl Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Var(var) => write!(f, "{}", var),
            Literal::Const(constant) => write!(f, "{}", constant)
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Function {
    NullaryFunction(Literal),
    BinaryFunction(BinaryFunction)
}

impl Funct for Function {
    fn arity(&self) -> u32 {
        match &self {
            Function::NullaryFunction(_) => 0,
            Function::BinaryFunction(_) => 2
        }
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Function::NullaryFunction(null) => write!(f, "{}", null),
            Function::BinaryFunction(bin) => write!(f, "{}", bin)
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum BinaryFunction {
    Add,
    Sub
}

impl Display for BinaryFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryFunction::Add => write!(f, "(+)"),
            BinaryFunction::Sub => write!(f, "(-)")
        }
    }
}


#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Predicate {
    LT,
    GT,
    EQ,
    LTE,
    GTE
}

impl Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let as_str = match self {
            Predicate::LT  => String::from("<"),
            Predicate::GT  => String::from(">"),
            Predicate::EQ  => String::from("="),
            Predicate::LTE => String::from("<="),
            Predicate::GTE => String::from(">=")
        };
        write!(f, "{}", as_str)
    }
}

impl Funct for Predicate {
    fn arity(&self) -> u32 {2}
}

impl Pred for Predicate {}

impl Predicate {
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
