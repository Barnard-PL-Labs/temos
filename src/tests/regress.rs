pub mod smt2;
pub mod sygus;

/*
 * TODO: instead of comparing string-for-string,
 * Pipe results of the formulae to cvc4 (using path)
 * and compare the results of cvc4 to its expected value (more robust)
 */
