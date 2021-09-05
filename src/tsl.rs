pub trait Funct {
    fn arity(self) -> u32;
}

pub trait Pred: Funct {
    fn evaluate(self) -> bool;
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct FunctionLiteral<T: Funct> {
    function: T,
    args: Vec< FunctionLiteral<T> >
}

//impl FunctionLiteral<T> {
//    fn validate_arity(self) {
//        let arity: u32 = self.function.arity();
//        if self.function.arity() != self.args.len() {
//            panic!("Arity mismatch!\n
//                   Function: {}, 
//                   Arity: {},
//                   Arguments: {}",
//                   self.function(), arity, self.args())
//        }
//    }
//}

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
    fn arity(self) -> u32 {2}
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

pub struct UpdateLiteral<T: Funct> {
    pub sink : Variable,
    pub update : FunctionLiteral<T>
}
