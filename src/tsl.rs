use std::fmt;
use std::fmt::Display;

pub trait LogicWritable {
    fn to_tsl(&self) -> String;
    fn to_smtlib(&self) -> String;
}

pub trait Funct: Display + Clone + LogicWritable {
    fn arity(&self) -> u32;
}

pub trait Pred : Funct + Display + Clone + LogicWritable {}

pub trait Theory : Clone + Copy {
    type FunctType: Funct;
    type PredType: Pred;
}

#[derive(Debug, Copy, Clone)]
pub enum TheoryFunctions<T: Theory> {
    Function(T::FunctType),
    Predicate(T::PredType),
    Connective(Connective)
}


impl<T> LogicWritable for TheoryFunctions<T> where T: Theory {
    fn to_tsl(&self) -> String {
        match self {
            TheoryFunctions::Function(f) => f.to_tsl(),
            TheoryFunctions::Predicate(p) => p.to_tsl(),
            TheoryFunctions::Connective(c) => c.to_tsl()
        }
    }
    fn to_smtlib(&self) -> String {
        match self {
            TheoryFunctions::Function(f) => f.to_smtlib(),
            TheoryFunctions::Predicate(p) => p.to_smtlib(),
            TheoryFunctions::Connective(c) => c.to_smtlib()
        }
    }
}

impl<T> Funct for TheoryFunctions<T> where T: Theory {
    fn arity(&self) -> u32 {
        match &self{
            TheoryFunctions::Function(f) => f.arity(),
            TheoryFunctions::Predicate(p) => p.arity(),
            TheoryFunctions::Connective(c) => c.arity(),
        }
    }
}

impl<T> Display for TheoryFunctions<T> where T: Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let as_str = match &self{
            TheoryFunctions::Function(f) => f.to_string(),
            TheoryFunctions::Predicate(p) => p.to_string(),
            TheoryFunctions::Connective(c) => c.to_string()
        }; 
        write!(f, "{}", as_str)
    }
}


#[derive(Clone)]
pub struct FunctionLiteral<T: Theory> {
    theory: T,
    pub function: TheoryFunctions<T>,
    pub args: Vec< FunctionLiteral<T> >
}

impl<T> Display for FunctionLiteral<T> where T: Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arg_vec : Vec<String> = self.args
            .iter()
            .map(|x| x.to_string())
            .collect();
        write!(f, "{} {}", self.function.to_string(), arg_vec.join(" "))
    }
}

impl<T> LogicWritable for FunctionLiteral<T> where T: Theory {
    fn to_tsl(&self) -> String {
        match &self.function {
            // For logical connectives
            TheoryFunctions::Connective(connective) => {
                match connective {
                    Connective::And => {
                        assert!(self.args.len() == 2,
                        "Expected arguments of length 2 for AND");
                        format!("({} && {})",
                                self.args[0].to_tsl(),
                                self.args[1].to_tsl())
                    },
                    Connective::Neg => {
                        assert!(self.args.len() == 1,
                        "Expected arguments of length 1 for NOT");
                        format!("!({})", self.args[0].to_tsl())
                    }
                }
            }

            // For general functions
            _ => {
                let arg_vec : Vec<String> = self.args
                    .iter()
                    .map(FunctionLiteral::to_tsl)
                    .collect();
                format!("{} {}", self.function.to_tsl(), arg_vec.join(" "))
            }
        }
    }
    fn to_smtlib(&self) -> String {
        if self.arity() == 0 {
            return format!("{}", self.function.to_smtlib());
        }
        let arg_vec : Vec<String> = self.args
            .iter()
            .map(|x| x.to_smtlib())
            .collect();
        format!("({} {})", self.function.to_smtlib(), arg_vec.join(" "))
    }
}

impl<T> Funct for FunctionLiteral<T> where T: Theory {
    fn arity(&self) -> u32 {
        self.function.arity()
    }
}

impl<T> FunctionLiteral<T> where T: Theory {
    pub fn new(theory: T,
               function: TheoryFunctions<T>,
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
    pub function_literal: FunctionLiteral<T>
}

impl<T> Display for PredicateLiteral<T> where T: Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.function_literal)
    }
}

impl<T> LogicWritable for PredicateLiteral<T> where T: Theory {
    fn to_tsl(&self) -> String {
        self.function_literal.to_tsl()
    }
    fn to_smtlib(&self) -> String {
        self.function_literal.to_smtlib()
    }
}

impl<T> PredicateLiteral<T> where T: Theory {
    pub fn new(theory : T,
               function: TheoryFunctions<T>,
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
                function: TheoryFunctions::Connective(Connective::Neg),
                args: vec![self.function_literal.clone()]
            }
        }
    }
    pub fn and(&self, other: &PredicateLiteral<T>) -> PredicateLiteral<T> {
        PredicateLiteral {
            function_literal: FunctionLiteral {
                theory: self.function_literal.theory,
                function: TheoryFunctions::Connective(Connective::And),
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

impl LogicWritable for Variable {
    fn to_tsl(&self) -> String {self.to_string()}
    fn to_smtlib(&self) -> String {self.to_string()}
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Variable::Variable(s) => write!(f, "{}", s)
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone, Copy)]
pub enum Connective {
    And,
    Neg
}

impl Display for Connective {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_smtlib())
    }
}

impl LogicWritable for Connective {
    fn to_tsl(&self) -> String {
        match self {
            Connective::And => String::from("&&"),
            Connective::Neg => String::from("!"),
        }
    }
    fn to_smtlib(&self) -> String {
        match self {
            Connective::And => String::from("and"),
            Connective::Neg => String::from("not"),
        }
    }
}

impl Funct for Connective {
    fn arity(&self) -> u32 {2}
}

impl Pred for Connective {}

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
