use std::fmt;
use std::fmt::{Debug, Display};
use std::rc::Rc;

pub trait Funct: Debug + Display {
    fn arity(&self) -> u32;
}

pub trait Pred : Funct + Debug + Clone {
}

pub trait Theory : Clone + Copy {
}

#[derive(Clone)]
pub struct FunctionLiteral<T: Theory> {
    theory: T,
    function: Rc<dyn Funct>,
    args: Vec< FunctionLiteral<T> >
}

impl<T> Display for FunctionLiteral<T> where T: Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arg_fmt_vector : Vec<String> = self.args
            .iter()
            .map(|x| x.to_string())
            .collect();
        let args_str = arg_fmt_vector.join(" ");
        write!(f, "{} {}", self.function, args_str)
    }
}

impl<T> FunctionLiteral<T> where T: Theory {
    pub fn new(theory: T,
               function: Rc<dyn Funct>,
               args : Vec< FunctionLiteral <T> >)
        -> FunctionLiteral<T> {
        let object = FunctionLiteral{
            theory,
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
pub struct PredicateLiteral<T: Theory> {
    function_literal: FunctionLiteral<T>
}

impl<T> Display for PredicateLiteral<T> where T: Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.function_literal)
    }
}

impl<T> PredicateLiteral<T> where T: Theory {
    // Cannot put Rc<dyn Pred> due to lack of trait upcasting in Rust
    // https://stackoverflow.com/q/28632968/13567582
    pub fn new(theory : T,
               function: Rc<dyn Funct>,
               args : Vec< FunctionLiteral<T> >)
        -> PredicateLiteral<T> {
        let object = FunctionLiteral{
            theory,
            function,
            args
        };
        object.validate_arity();
        PredicateLiteral {
            function_literal: object
        }
    }
    pub fn negate(&self) -> PredicateLiteral<T> {
        PredicateLiteral {
            function_literal: FunctionLiteral {
                theory: self.function_literal.theory,
                function: Rc::new(Connective::Neg),
                args: vec![self.function_literal.clone()]
            }
        }
    }
    pub fn and(&self, other: &PredicateLiteral<T>) -> PredicateLiteral<T> {
        PredicateLiteral {
            function_literal: FunctionLiteral {
                theory: self.function_literal.theory,
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

pub struct UpdateLiteral<T: Theory> {
    pub sink : Variable,
    pub update : FunctionLiteral<T>
}
