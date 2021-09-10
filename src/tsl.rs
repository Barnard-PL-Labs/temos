use std::fmt::Debug;
use std::rc::Rc;

pub trait Funct: Debug {
    fn arity(&self) -> u32;
}

pub trait Pred : Funct + Debug + Clone {
    fn evaluate(&self) -> bool;
}

#[derive(Debug, Clone)]
pub struct FunctionLiteral {
    function: Rc<dyn Funct>,
    args: Vec<FunctionLiteral>
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
                   Function: {:?}, 
                   Arity: {},
                   Arguments: {:?}",
                   self.function, arity, self.args)
        }
    }
}

#[derive(Debug, Clone)]
pub struct PredicateLiteral {
    function_literal: FunctionLiteral
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

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Connective {
    And,
    Neg
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
