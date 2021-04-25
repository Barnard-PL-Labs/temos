pub use Temporal::*;
pub use Literal::*;
pub use Update::*;
pub use Predicate::*;
pub use LogicOp::*;
pub use LiaOp::*;
use std::rc::Rc;
use std::collections::HashSet;
use crate::utils;

pub enum Temporal {
    Next(i32),
    Liveness
}

#[derive(Hash, Eq, PartialEq, Clone)]
pub enum Literal {
    Var(String),
    Const(i32),
}

impl Literal {
    fn to_string(&self) -> String {
        match self {
            Var(string) => String::from(string),
            Const(val)  => format!("{}", val)
        }
    }
}

pub enum LiaOp {
    Add,
    Sub
}

impl LiaOp {
    fn to_string(&self) -> String {
        match self {
            Add => String::from("+"),
            Sub => String::from("-")
        }
    }
}

pub enum Update {
    Function(LiaOp, Literal, Literal),
    Signal(Literal)
}

impl Update {
    fn to_sygus(&self) -> String {
        match self {
            Function(op, lhs, rhs) => 
                format!("({} {} {})", 
                        op.to_string(),
                        lhs.to_string(),
                        rhs.to_string()),
            Signal(val) => val.to_string()
        }
    }
}

#[derive(Hash, Eq, PartialEq, Clone)]
pub enum LogicOp {
    LT,
    EQ
}

impl LogicOp {
    fn to_string(&self) -> String {
        match self {
            LT => String::from("<"),
            EQ => String::from("=")
        }
    }
}

#[derive(Hash, Eq, PartialEq, Clone)]
pub enum Predicate {
    And(Rc<Predicate>, Rc<Predicate>),
    Neg(Rc<Predicate>),
    Bool(LogicOp, Literal, Literal)
}


impl Predicate {
    // TODO: need standardization, i.e. var always on LHS
    fn to_precond(&self) -> String {
        match self {
            Bool(op, _, rhs) =>
                match op {
                    EQ => format!("(function {})", rhs.to_string()),
                    LT => panic!("Not Implemented Error")  // forall
                }
            _ => panic!("Not Implemented Error")
        }
    }

    // TODO: need standardization, i.e. var always on LHS
    fn to_constraint(&self, precond: &Predicate) -> String {
        let mut sygus_str = String::from("(constraint ");
        let constraint = match self {
            Bool(op, _, rhs) => format!("({} {} {})",
                    op.to_string(),
                    precond.to_precond(),
                    rhs.to_string()),
            _ => panic!("Not Implemented Error")

        };
        sygus_str.push_str(&constraint);
        sygus_str.push_str(")\n");
        sygus_str 
    }

    fn to_smtlib(&self) -> String {
        let mut smt_str = String::from("");
        let pred_str = match self {
            Bool(op, lhs, rhs) => 
                format!("({} {} {})",
                op.to_string(),
                lhs.to_string(),
                rhs.to_string()),
            And(lhs, rhs) =>
                format!("(and {} {})",
                lhs.to_smtlib(),
                rhs.to_smtlib()),
            Neg(pred) => 
                format!("(not {})",
                pred.to_smtlib())
        };
        smt_str.push_str(&pred_str);
        smt_str 
    }

    fn to_assert(&self) -> String {
        format!("(assert {})\n", self.to_smtlib())
    }

    fn get_vars(&self) -> HashSet<&str> {
        let mut vars : HashSet<&str> = HashSet::new();
        match self {
            Bool(_, lhs, rhs) => {
                match lhs {
                    Var(var) => {vars.insert(&var); ()}
                    _ => ()
                };
                match rhs {
                    Var(var) => {vars.insert(&var); ()}
                    _ => ()
                }
            },
            And(lhs, rhs) => {
                vars = vars.union(&lhs.get_vars()).cloned().collect();
                vars = vars.union(&rhs.get_vars()).cloned().collect();
            },
            Neg(pred) => {vars = vars.union(&pred.get_vars()).cloned().collect();}
        };
        vars
    }

    pub fn to_smt2(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        let vars = self.get_vars();

        for variable in &vars {
            query.push_str(&format!("(declare-const {} Int)\n", variable));
        }

        query.push_str("\n");
        query.push_str(&self.to_assert());
        query.push_str("(check-sat)\n");
        query
    }

    pub fn is_unsat(&self) -> bool {
        let smt2 = self.to_smt2();
        let result = utils::run_cvc4(smt2, "smt");
        if result == "sat\n" {
            return false
        } else if result == "unsat\n" {
            return true
        } else {
            panic!("not sat or unsat??\n")
        }
    }

    fn to_tsl(&self) -> String {
        match self {
            Bool(op, lhs, rhs) => 
                format!("({} {} {})",
                op.to_string(),
                lhs.to_string(),
                rhs.to_string()),
            And(lhs, rhs) =>
                format!("({} && {})",
                lhs.to_tsl(),
                rhs.to_tsl()),
            Neg(pred) => format!("!{}", pred.to_tsl())
        }
    }

    pub fn to_assumption(&self) -> String {
        format!("!{}", self.to_tsl())
    }

    pub fn and(&self, pred: &Predicate) -> Predicate {
        And(Rc::new(self.clone()), Rc::new(pred.clone()))
    }
    pub fn neg(&self) -> Predicate {
        Neg(Rc::new(self.clone()))
    }
}

pub struct SygusHoareTriple {
    pub precond: Predicate,
    pub postcond: Predicate,
    pub var_name: String,
    pub temporal: Temporal,
    pub updates: Vec<Update>,
}

impl SygusHoareTriple {
    pub fn to_sygus(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        let header = format!("(synth-fun function (({} Int)) Int\n", self.var_name);
        query.push_str(&header);
        query.push_str("\t((I Int))(\n");
        query.push_str("\t\t(I Int (\n");
        for update_term in &self.updates {
            query.push_str(&format!("\t\t\t\t{}\n", update_term.to_sygus()));
            // TODO: implement (- I 1)
        }
        query.push_str("\t\t\t)\n");
        query.push_str("\t\t)\n");
        query.push_str("\t)\n");
        query.push_str(")\n");
        query.push_str(&self.postcond.to_constraint(&self.precond));
        query.push_str("(check-synth)\n");
        query
    }

    pub fn cmd_options(&self) -> String {
        match self.temporal {
            Next(timesteps) => format!("--sygus-abort-size={}", timesteps),
            Liveness => panic!("Not Implemented Error")
        }
    }
}
