use crate::types::*;
use std::fs;

#[test]
fn test_sygus() {
    let result;
    let expected;
    let updates;

    expected = fs::read_to_string("src/tests/regress/sygus.sl").unwrap();

    updates = vec![Function(Add, Var("x".to_string()), Const(1)),
        Function(Sub, Var("x".to_string()), Const(1)),
        Signal(Var("x".to_string()))];

    let hoare = SygusHoareTriple {
        precond  : Bool(EQ, Var("x".to_string()), Const(0)),
        postcond : Bool(EQ, Var("x".to_string()), Const(1)),
        var_name: "x".to_string(),
        temporal: Next(1),
        updates: updates
    };

    result = hoare.to_sygus();

    assert_eq!(expected, result);
}
