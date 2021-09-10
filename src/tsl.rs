use std::fmt;
use std::fmt::{Debug, Display};
use std::rc::Rc;

pub trait Funct: Debug + Display {
    fn arity(&self) -> u32;
}

pub trait Pred : Funct + Debug + Clone {
    fn evaluate(&self) -> bool;
}

#[derive(Clone)]
pub struct FunctionLiteral {
    function: Rc<dyn Funct>,
    args: Vec<FunctionLiteral>
}

impl Display for FunctionLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arg_fmt_vector : Vec<String> = self.args
            .iter()
            .map(|x| x.to_string())
            .collect();
        let args_str = arg_fmt_vector.join(" ");
        write!(f, "{} {}", self.function, args_str)
    }
}


impl FunctionLiteral {
    pub fn new(function: Rc<dyn Funct>,
               args : Vec<FunctionLiteral>)
        -> FunctionLiteral {
        let object = FunctionLiteral{
            function,
            args
        };
        object.validate_arity();
        object
    }
    fn validate_arity(&self) {
        let arity: u32 = self.function.arity();
        let arg_len : u32 = self.args.len() as u32;
        if arity != arg_len {
            panic!("Arity mismatch!\n
                   Arity: {},
                   Literal: {}",
                   arity, self)
        }
    }
}

#[derive(Clone)]
pub struct PredicateLiteral {
    function_literal: FunctionLiteral
}

impl Display for PredicateLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.function_literal)
    }
}

impl PredicateLiteral {
    // Cannot put Rc<dyn Pred> due to lack of trait upcasting in Rust
    // https://stackoverflow.com/q/28632968/13567582
    pub fn new(function: Rc<dyn Funct>,
               args : Vec<FunctionLiteral>)
        -> PredicateLiteral {
        let object = FunctionLiteral{
            function,
            args
        };
        object.validate_arity();
        PredicateLiteral {
            function_literal: object
        }
    }
    pub fn negate(&self) -> PredicateLiteral {
        PredicateLiteral {
            function_literal: FunctionLiteral {
                function: Rc::new(Connective::Neg),
                args: vec![self.function_literal.clone()]
            }
        }
    }
    pub fn and(&self, other: &PredicateLiteral) -> PredicateLiteral {
        PredicateLiteral {
            function_literal: FunctionLiteral {
                function: Rc::new(Connective::And),
                args: vec![
                    self.function_literal.clone(),
                    other.function_literal.clone()
                ]
            }
        }
    }
}


#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Variable {
    Variable(String)
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Variable::Variable(s) => write!(f, "{}", s)
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Connective {
    And,
    Neg
}

impl Display for Connective {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Connective::And => write!(f, "{}", "AND"),
            Connective::Neg => write!(f, "{}", "NOT")
        }
    }
}

impl Funct for Connective {
    fn arity(&self) -> u32 {2}
}

impl Pred for Connective {
    fn evaluate(&self) -> bool {
        panic!("Not Implemented Error")
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum PredicateTerm<T> {
    PredicateTerm(T),
    Connective(Connective)
}

#[derive(Debug, Clone)]
pub enum Temporal {
    Next(u32),
    Eventually
}

pub struct UpdateLiteral {
    pub sink : Variable,
    pub update : FunctionLiteral
}
