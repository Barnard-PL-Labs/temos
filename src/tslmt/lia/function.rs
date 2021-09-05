#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum LiaFunction {
    Literal(Literal),
    BinaryFunction(BinaryFunction)
}

enum BinaryFunction {
    Add,
    Sub
}


#[derive(Debug, Hash, Eq, PartialEq, Clone)]
enum Literal {
    Var(String),
    Const(i32),
}
