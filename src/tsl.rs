use std::fmt::Debug;

pub trait Funct: Debug {
    fn arity(&self) -> u32;
}

pub trait Pred: Funct {
    fn evaluate(self) -> bool;
}

// FIXME: type-check preds vs functs @ compile time
#[derive(Debug)]
pub struct FunctionLiteral {
    function: Box<dyn Funct>,
    args: Vec<FunctionLiteral>
}

impl FunctionLiteral {
    pub fn new(function: Box<dyn Funct>,
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
