use crate::tsl::{Funct, Pred, Variable, Theory};
use crate::tsl::{PredicateLiteral, LogicWritable};
//use crate::cvc4;
use std::fmt;
use std::fmt::Display;

#[derive(Debug, Clone, Copy)]
pub enum Lia {LIA}
impl Theory for Lia {
    type FunctType = Function;
    type PredType = Predicate;
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Literal {
    Var(Variable),
    Const(i32),
}

impl LogicWritable for Literal {
    fn to_tsl(&self) -> String {
        match self {
            Literal::Var(variable) => variable.to_tsl(),
            Literal::Const(constant) => constant.to_string()
        }
    }
    fn to_smtlib(&self) -> String {
        match self {
            Literal::Var(variable) => variable.to_smtlib(),
            Literal::Const(constant) => constant.to_string()
        }
    }
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

impl LogicWritable for Function {
    fn to_tsl(&self) -> String {
        match self {
            Function::NullaryFunction(literal) => literal.to_tsl(),
            Function::BinaryFunction(binop) => binop.to_tsl()
        }
    }
    fn to_smtlib(&self) -> String {
        match self {
            Function::NullaryFunction(literal) => literal.to_smtlib(),
            Function::BinaryFunction(binop) => binop.to_smtlib()
        }
    }
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
            Function::NullaryFunction(literal) => write!(f, "{}", literal),
            Function::BinaryFunction(bin) => write!(f, "{}", bin)
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum BinaryFunction {
    Add,
    Sub
}

impl LogicWritable for BinaryFunction {
    fn to_tsl(&self) -> String {
        match self {
            BinaryFunction::Add => String::from("add"),
            BinaryFunction::Sub => String::from("sub"),
        }
    }
    fn to_smtlib(&self) -> String {
        match self {
            BinaryFunction::Add => String::from("+"),
            BinaryFunction::Sub => String::from("-"),
        }
    }
}

impl Display for BinaryFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})", self.to_smtlib())
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
        write!(f, "{}", self.to_smtlib())
    }
}

impl LogicWritable for Predicate {
    fn to_tsl(&self) -> String {
        match self {
            Predicate::LT  => String::from("lt"),
            Predicate::GT  => String::from("gt"),
            Predicate::EQ  => String::from("eq"),
            Predicate::LTE => String::from("lte"),
            Predicate::GTE => String::from("gte")
        }
    }
    fn to_smtlib(&self) -> String {
        match self {
            Predicate::LT  => String::from("<"),
            Predicate::GT  => String::from(">"),
            Predicate::EQ  => String::from("="),
            Predicate::LTE => String::from("<="),
            Predicate::GTE => String::from(">=")
        }
    }
}

impl Funct for Predicate {
    fn arity(&self) -> u32 {2}
}

impl Pred for Predicate {}

impl PredicateLiteral<Lia> {
    fn evaluate(&self) -> bool {
        panic!("")
    }
    pub fn to_tsl_assumption(&self) -> String {
        format!("!{};", self.to_tsl())
    }
}
