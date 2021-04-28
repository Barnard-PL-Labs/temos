pub use Temporal::*;
pub use Literal::*;
pub use UpdateTerm::*;
pub use Predicate::*;
pub use LogicOp::*;
pub use LiaOp::*;
use std::fs;
use std::rc::Rc;
use std::collections::HashSet;
use crate::utils;
use crate::predicate;
use crate::hoare;
use crate::sygus;
use std::convert::TryInto;

#[derive(Clone)]
pub enum Temporal {
    Next(u32),
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
    fn to_function(&self, var_exchange: &str) -> Literal {
        match self {
            Var(var_name) => {
                if var_name == var_exchange {
                    Var(format!("(function {})", var_name))
                } else {
                    Var(var_name.to_string())
                }
            },
            Const(val) => Const(*val)
        }
    }
    fn change_name(&self, new_name: &str) -> Literal {
        match self {
            Var(var_name) => Var(String::from(new_name)),
            Const(val) => Const(*val)
        }
    }
}

#[derive(Hash, Eq, PartialEq, Clone)]
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

#[derive(Hash, Eq, PartialEq, Clone)]
pub enum UpdateTerm {
    Function(LiaOp, Literal, Literal),
    Signal(Literal)
}

impl UpdateTerm {
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
    fn change_sink_name(&self, new_name: &str) -> UpdateTerm {
        match self {
            Function(op, lhs, rhs) =>
                Function(op.clone(),
                         lhs.change_name(new_name),
                         rhs.change_name(new_name)),
            Signal(var) => Signal(var.clone())
        }
    }
}

#[derive(Hash, Eq, PartialEq, Clone)]
pub enum LogicOp {
    LT,
    EQ,
    LTE,
    GT
}

impl LogicOp {
    fn to_string(&self) -> String {
        match self {
            LT  => String::from("<"),
            EQ  => String::from("="),
            LTE => String::from("<="),
            GT => String::from(">=")
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
    pub fn is_eq(&self) -> bool {
        match self {
            Bool(op, _, _) => match op {
                EQ => true,
                _  => false
            }
            // Assuming that we have elided UNSAT preds.
            And(lpred, _) => false,
            Neg(pred) => pred.is_eq()
        }
    }
    // XXX: no real support for two-element predicates yet.
    pub fn get_var_name(&self) -> String {
        match self {
            Bool(_, lhs, _) =>
                match lhs {
                    Var(s) => String::from(s),
                    Const(_) => panic!("Non-rhs argument not supported.")
                },
            And(lpred, _) => lpred.get_var_name(),
            Neg(pred) => pred.get_var_name()
        }
    }

    fn var_to_function(self, var_name: &str) -> Predicate {
        match self {
            Bool(op, lhs, rhs) =>
                Bool(op,
                     lhs.to_function(var_name),
                     rhs.to_function(var_name)),
            And(larg, rarg) =>
                Predicate::new_and((*larg).clone()
                                       .var_to_function(var_name),
                                   (*rarg).clone()
                                       .var_to_function(var_name)),
            Neg(pred) =>
                Predicate::new_neg((*pred).clone()
                    .var_to_function(var_name))
        }
    }

    fn to_smtlib(&self) -> String {
        let mut smt_str = String::new();
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

    fn to_constraint(&self) -> String {
        format!("(constraint {})\n", self.to_smtlib())
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
            Neg(pred) => {
                vars = vars.union(&pred.get_vars()).cloned().collect();
            }
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
        let result = utils::cvc4_generic(smt2, "smt");
        if result == "sat\n" {
            return false
        } else if result == "unsat\n" {
            return true
        } else {
            panic!("not sat or unsat??\n")
        }
    }

    pub fn is_sat(&self) -> bool {
        !self.is_unsat()
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
        format!("!{};", self.to_tsl())
    }

    pub fn and(&self, pred: &Predicate) -> Predicate {
        And(Rc::new(self.clone()), Rc::new(pred.clone()))
    }

    pub fn neg(&self) -> Predicate {
        Neg(Rc::new(self.clone()))
    }

    pub fn new_and(larg: Predicate, rarg: Predicate) -> Predicate {
        And(Rc::new(larg.clone()), Rc::new(rarg.clone()))
    }

    pub fn new_neg(pred: Predicate) -> Predicate {
        Neg(Rc::new(pred.clone()))
    }
}

// TODO: Might need var info...
#[derive(Clone)]
pub struct SpecPredicate {
    pub pred: Predicate,
    pub temporal: Vec<Temporal>
}

#[derive (Clone, Eq, PartialEq)]
pub struct Update {
    pub update_term: UpdateTerm,
    pub var_name: String,
    pub depends: Vec<String>
}

pub struct SygusHoareTriple {
    pub precond : Rc<Predicate>,
    pub postcond: Rc<Predicate>,
    pub var_name: String,
    pub temporal: Rc<Temporal>,
    pub updates: Rc<HashSet<UpdateTerm>>,
}

// TODO: support multiple variables as inputs
impl SygusHoareTriple {
    fn quantified_constraint(&self) -> String {
        let var_name = self.precond.get_var_name();
        let mut constraint = format!("(constraint (forall (({} Int))\n", var_name);
        let postcond = (*self.postcond).clone().
            var_to_function(&var_name);
        constraint.push_str(&format!("\t(=> {}\n", self.precond.to_smtlib()));
        constraint.push_str(&format!("\t{}\n", postcond.to_smtlib()));
        constraint.push_str(")))\n");
        constraint
    }
    pub fn to_sygus(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        let var_name = self.precond.get_var_name();
        let header = format!("(synth-fun function (({} Int)) Int\n", self.var_name);
        let variables = self.postcond.get_vars();
        let postcond = (*self.postcond).clone().
            var_to_function(&var_name);
        let quantifier_free = self.precond.is_eq();

        if quantifier_free {
            for var in &variables {
                query.push_str(&format!("(declare-const {} Int)\n", var));
            }
        }

        query.push_str(&header);

        query.push_str("\t((I Int))(\n");
        query.push_str("\t\t(I Int (\n");
        for update_term in &*self.updates {
            query.push_str(&format!("\t\t\t\t{}\n", update_term.to_sygus()));
            query.push_str(&format!("\t\t\t\t{}\n",
                                    update_term.change_sink_name("I")
                                        .to_sygus()));
        }
        query.push_str("\t\t\t)\n");
        query.push_str("\t\t)\n");
        query.push_str("\t)\n");
        query.push_str(")\n");

        if quantifier_free {
            query.push_str(&self.precond.to_assert());
            query.push_str(&postcond.to_constraint());
        } else {
            query.push_str(&self.quantified_constraint());
        }
        query.push_str("(check-synth)\n");
        query
    }

    fn run_synthesis(&self) -> String {
        match *self.temporal {
            Next(timestep) => {
                utils::sygus_cvc4(self.to_sygus(),"sygus", timestep)
            }
            Liveness => panic!("")  // TODO
        }
    }

    fn to_assumption(&self) -> Option<String> {
        let sygus_result = sygus::get_sygus_result(&self.run_synthesis());
        if sygus_result.is_none() {
            return None;
        }
        let timesteps = match *self.temporal {
            Next(i) => format!(") -> {}",
                               "X ".repeat(i.try_into()
                                   .unwrap())),
            Liveness => format!("W {}) -> F",
                                self.postcond.to_tsl())
        };
        Some(format!("{} && ({} {} {};",
                     self.precond.to_tsl(),
                     sygus_result.unwrap(),
                     timesteps,
                     self.postcond.to_tsl()))
    }
}

pub struct Specification {
    pub predicates: Vec<SpecPredicate>,
    pub updates: Vec<Update>
}

impl Specification {
    pub fn write_assumption(&self, file_name: &str) {
        let assumption = self.to_assumption();
        fs::write(file_name, assumption).unwrap();
    }
    pub fn to_assumption(&self) -> String {
        let mut assumptions = String::new();
        let predicates = self.predicates.iter()
            .map(|x| x.pred.clone())
            .collect();
        let hoare_vec;
        let sygus_results: Vec<String>;

        for pred_ass in predicate::gen_assumptions(predicates) {
            assumptions.push_str(&format!("{}\n", pred_ass));
        }
        hoare_vec = hoare::enumerate_hoare(self.predicates.clone(),
                                           self.updates.clone());
        sygus_results = hoare_vec.iter()
            .filter_map(|x| x.to_assumption())
            .collect();
        for result in sygus_results {
            let sygus_ass = sygus::fxn_to_tsl(result);
            assumptions.push_str(&sygus_ass);
            assumptions.push('\n');
        }
        assumptions
    }
}