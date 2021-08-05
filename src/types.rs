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
use crate::parser::smt_sygus as parser;
use std::convert::TryInto;

const TIMEOUT_DEPTH: u32 = 10;

#[derive(Debug, Clone)]
pub enum Temporal {
    Next(u32),
    Liveness
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Literal {
    Var(String),
    Const(i32),
}

impl Literal {
    fn to_string(&self) -> String {
        match self {
            Var(string) => String::from(string),
            Const(val)  => {
                if val < &0 {
                    format!("(- {})", -1 * *val)
                } else {
                    format!("{}", *val)
                }
            } 
        }
    }
    fn to_tsl(&self) -> String {
        match self {
            Var(string) => String::from(string),
            Const(val)  => format!("c{}()", val)
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
            Var(_) => Var(String::from(new_name)),
            Const(val) => Const(*val)
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
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
    fn to_tsl(&self) -> String {
        match self {
            Add => String::from("add"),
            Sub => String::from("sub")
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
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

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum LogicOp {
    LT,
    GT,
    EQ,
    LTE,
    GTE
}

impl LogicOp {
    fn to_string(&self) -> String {
        match self {
            LT  => String::from("<"),
            GT  => String::from(">"),
            EQ  => String::from("="),
            LTE => String::from("<="),
            GTE => String::from(">=")
        }
    }
    fn to_tsl(&self) -> String {
        match self {
            LT  => String::from("lt"),
            GT  => String::from("gt"),
            EQ  => String::from("eq"),
            LTE => String::from("lte"),
            GTE => String::from("gte")
        }
    }
    fn reverse(&self) -> LogicOp {
        match self {
            LT  => GTE,
            GT  => LTE,
            LTE => GT,
            GTE => LT,
            EQ  => panic!("No reversal for EQ")
        }
    }
    fn is_lt(&self) -> bool {
        match self {
            LT  => true,
            LTE => true,
            _   => false
        }
    }
    fn is_gt(&self) -> bool {
        match self {
            GT  => true,
            GTE => true,
            _   => false
        }
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
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
            And(_, _) => false,
            Neg(_) => false
        }
    }
    fn is_two_var(&self) -> bool {
        match self {
            Bool(_, lhs, rhs) =>
                match lhs {
                    Const(_) => false,
                    Var(_) => match rhs {
                        Var(_)   => true,
                        Const(_) => false
                    }
                },
                And(_, _) => panic!("Not Implemented Error"),
                Neg(pred) => pred.is_two_var()
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

    pub fn to_smt2_get_model(&self, ignore_models: &Vec<i32>) 
        -> String {
        let mut query = String::from("(set-logic LIA)\n");
        query.push_str("(set-option :produce-models true)\n");
        let vars = self.get_vars();

        for variable in &vars {
            query.push_str(&format!("(declare-const {} Int)\n", variable));
        }

        query.push_str("\n");
        for ignore_val in ignore_models {
            let model_val;
            if ignore_val < &0 {
                model_val = format!("(- {})", -1 * ignore_val);
            } else {
                model_val = format!("{}", ignore_val);
            }
            query.push_str(&format!("(assert (not (= {} {})))\n",
                                    self.get_var_name(),
                                    model_val));
        }
        query.push_str(&self.to_assert());
        query.push_str("(check-sat)\n");
        query.push_str("(get-model)\n");
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
            panic!("not sat or unsat??\n
                   Result:{}\n", result);
        }
    }

    pub fn is_sat(&self) -> bool {
        !self.is_unsat()
    }

    fn to_tsl(&self) -> String {
        match self {
            Bool(op, lhs, rhs) =>
                format!("({} {} {})",
                op.to_tsl(),
                lhs.to_tsl(),
                rhs.to_tsl()),
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

    fn generate_pbe(&self, num_ex: u32) -> Vec<Predicate> {
        let mut models : Vec<i32> = Vec::new();
        let mut pbe_preds: Vec<Predicate> = Vec::new();

        if self.is_eq() {
            panic!("Generate PBE called with equality\n");
        }

        for _ in 0..num_ex {
            let smt_query = self.to_smt2_get_model(&models);
            let model = utils::cvc4_generic(smt_query, "smt");
            let model_val = parser::parse_model(&model);
            models.push(model_val);
        }
        for pbe_model in models {
            let pbe_pred = Bool(EQ,
                                Var(self.get_var_name()),
                                Const(pbe_model));
            pbe_preds.push(pbe_pred);
        }
        pbe_preds
    }
}

#[derive(Debug, Clone)]
pub struct SpecPredicate {
    pub pred: Predicate,
    pub temporal: Vec<Temporal>
}

#[derive(Debug, Clone, Eq, PartialEq)]
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
        let mut const_vars : HashSet<&str> = HashSet::new();

        // If the precond-var is not part of a forall clause
        if quantifier_free {
            for var in &variables {
                const_vars.insert(var);
            }
        }
        // Yes, I know this is repeated
        // Add all variables that aren't part of the function
        for var in &variables {
            if !(var.eq(&var_name)) {
                const_vars.insert(var);
            }
        }

        for var in const_vars {
            query.push_str(&format!("(declare-const {} Int)\n", var));
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

    fn to_hack_sygus(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        query.push_str(&format!("(declare-const {} Int)\n", self.precond.get_var_name()));
        let header = format!("(synth-fun function (({} Int)) Int\n", self.var_name);
        if !self.precond.is_eq() {
            panic!("Not Implemented Error");
        }
        query.push_str(&header);

        let model: i32;
        let const_int = 5;
        let mut is_neg = false;

        match &*self.precond {
            Bool(_, _, rhs) => {
                match rhs {
                    Const(x) => {model = *x;}
                    _ => panic!("hack failed.")
                }
            },
            Neg(pred) => match &**pred {
                Bool(_, _, rhs) => {
                    match rhs {
                        Const(x) => {model = *x;}
                        _ => panic!("Got precond {}", self.precond.to_smtlib())
                    }
                },
                _ => panic!("hack failed.")
            }
            _ => panic!("Got precond {}", self.precond.to_smtlib())
        };

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

        query.push_str(&self.precond.to_assert());
        { 
            let operator;
            let var_name;
            match &*self.postcond {      
                Bool(op, _, rhs) => {
                    operator = op;
                    match &*rhs {
                        Var(s) => {var_name = s},
                        _ => panic!("hack failed.")
                    };
                },
                Neg(pred) => {
                    is_neg = true;
                    match &**pred {
                        Bool(op, _, rhs) => {
                            operator = op;
                            match &*rhs {
                                Var(s) => {var_name = s},
                                _ => panic!("hack failed.")
                            };
                        },
                        _ => panic!("hack failed.")
                    }
                },
                _ => panic!("hack failed.")
            };
            let mut constraint = format!("(constraint (forall (({} Int))\n", var_name);
            let val;
            if operator.is_lt() {
                val = model - const_int;
            } else if operator.is_gt() {
                val = model + const_int;
            } else {
                panic!("hack failed.");
            }
            let val = Const(val);
            constraint.push_str(&format!("\t(=> ({} {} {})\n",
                                         operator.reverse().to_string(),
                                         var_name,
                                         val.to_string(),
                                         ));
            if !is_neg {
                constraint.push_str(&format!("\t({} (function {}) {})\n",
                operator.to_string(),
                self.precond.get_var_name(),
                var_name
                ));
            } else {
                constraint.push_str(&format!("\t(not ({} (function {}) {}))\n",
                operator.to_string(),
                self.precond.get_var_name(),
                var_name
                ));
            }
            constraint.push_str(")))\n");
            query.push_str(&constraint);
        }
        query.push_str("(check-synth)\n");
        query
    }

    fn verify_loop(&self, loop_body: &str) {
        match *self.temporal {
            Next(_) => panic!("This should not be called for safety specs\n"),
            _ => ()
        };
        if (*self.precond).is_eq() {
            panic!("Should not be called for equalities\n");
        }
        assert_eq!(loop_body, loop_body);
    }

    fn run_synthesis(&self) -> String {
        match *self.temporal {
            Next(timestep) => {
                utils::sygus_cvc4(self.to_sygus(), "sygus2", timestep)
            }
            Liveness => {
                if (*self.precond).is_eq() {
                    // XXX
                    if (*self.postcond).is_two_var(){
                        let sygus = self.to_hack_sygus();
                        let result = utils::sygus_cvc4(sygus, "sygus2", TIMEOUT_DEPTH);
                        result
                    }
                    else {
                        utils::sygus_cvc4(self.to_sygus(), "sygus2",
                        TIMEOUT_DEPTH)
                    }
                } 
                // while loops with PBE
                else {
                    let pred_pbe_vec = (*self.precond).generate_pbe(3);
                    let mut sygus_results = Vec::new();
                    let while_loop : Option<String>;
                    for pred_pbe in pred_pbe_vec {
                        let hoare_pbe = SygusHoareTriple {
                            precond: Rc::new(pred_pbe),
                            postcond: Rc::clone(&self.postcond),
                            var_name: self.var_name.clone(),
                            temporal: Rc::clone(&self.temporal),
                            updates: Rc::clone(&self.updates)
                        };
                        sygus_results.push(hoare_pbe.run_synthesis());
                    }
                    while_loop = parser::get_while_loop(sygus_results);
                    match while_loop {
                        None => "".to_string(),
                        Some(body) => {
                            self.verify_loop(&body);
                            // XXX
                            format!("unsat\n(define-fun function ((x Int)) Int {})",
                                    body)
                        }
                    }
                }
            }
        }
    }

    fn to_assumption(&self) -> Option<String> {
        let sygus_result = parser::get_sygus_result(&self.run_synthesis());
        if sygus_result.is_none() {
            return None;
        }
        let update_ass = parser::fxn_to_tsl(sygus_result.unwrap());
        let timesteps = match *self.temporal {
            Next(i) => format!(") -> {}",
            "X ".repeat(i.try_into()
                        .unwrap())),
            Liveness => format!(" W {}) -> F",
            self.postcond.to_tsl())
        };
        let foo = format!("{} && ({}{} {};", self.precond.to_tsl(),
                     update_ass,
                     timesteps,
                     self.postcond.to_tsl());
        Some(foo)
    }
}

#[derive(Debug)]
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
            assumptions.push_str(&result);
            assumptions.push('\n');
        }
        assumptions
    }
    pub fn to_always_assume(&self) -> String {
        let header = "always assume{";
        let ass = self.to_assumption();
        [header, &ass, "}"].join("\n")
    }
}
