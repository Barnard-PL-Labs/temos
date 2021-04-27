use crate::types::*;
use crate::utils;

#[test]
fn test_sygus() {
    let updates;
    let result;
    let expected = "unsat\n(define-fun function ((x Int)) Int (+ x 1))\n";

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

    let query = hoare.to_sygus();

    result = utils::cvc4_generic(query, "sygus");

    assert_eq!(expected, result);
}
