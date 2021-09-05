#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct FunctionLiteral<T> {
    function: T,
    args: Vec<FunctionLiteral>
}
