mod types; 
mod assumption;
mod predicate;
pub use crate::types::*;

fn test_sygus() {
    let updates = vec![Function(Add, Var("x".to_string()), Const(1)),
                       Function(Sub, Var("x".to_string()), Const(1)),
                       Signal(Var("x".to_string()))];
    let hoare = SygusHoareTriple {
        precond  : Bool(EQ, Var("x".to_string()), Const(0)),
        postcond : Bool(EQ, Var("x".to_string()), Const(1)),
        var_name: "x".to_string(),
        temporal: Next(1),
        updates: updates
    };
    println!("{}", hoare.to_sygus());
    println!("{}", hoare.cmd_options());
}

fn main() {
    test_sygus();
    assumption::test_assumption();
    predicate::test_predicates();
}
