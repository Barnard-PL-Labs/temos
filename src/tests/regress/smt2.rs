use crate::types::*;
use std::fs;

#[test]
pub fn test_smt2_1() {
    let expected = fs::read_to_string("src/tests/regress/smt2_1.smt2").unwrap();
    let predicate = Bool(LT, Var("x".to_string()), Const(5));
    let result = predicate.to_smt2();
    assert_eq!(expected, result);
}

#[test]
pub fn test_smt2_2() {
    let expected = fs::read_to_string("src/tests/regress/smt2_2.smt2").unwrap();
    let predicate = Bool(LT, Var("x".to_string()), Var("y".to_string()));
    let result = predicate.to_smt2();
    assert_eq!(expected, result);
}
