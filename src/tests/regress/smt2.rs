use crate::types::*;
use crate::utils;

#[test]
pub fn test_smt2_1() {
    let expected = "unsat\n";
    let predicate = Bool(EQ, Const(4), Const(5));
    let result = utils::cvc4_generic(predicate.to_smt2(), "smt2");
    assert_eq!(expected, result);
}

#[test]
pub fn test_smt2_2() {
    let expected = "sat\n";
    let predicate = Bool(LT, Var("x".to_string()), Var("y".to_string()));
    let result = utils::cvc4_generic(predicate.to_smt2(), "smt2");
    assert_eq!(expected, result);
}
