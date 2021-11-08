use std::collections::HashSet;
use std::rc::Rc;
use std::fmt;
use std::fmt::Display;
use crate::theories::lia::Lia;
use crate::tsl::{Temporal, Variable, Theory};
use crate::tsl::{FunctionLiteral, PredicateLiteral, UpdateLiteral};
use crate::tsl::LogicWritable;
use crate::cvc4;

/// Data Transformation Obligation.
pub struct Dto<T: Theory> {
    pub precond: Rc< PredicateLiteral<T> >,
    pub postcond: Rc< PredicateLiteral<T> >,
    pub temporal: Temporal,
    pub grammar: Vec< UpdateLiteral<T> >
}

impl<T> Display for Dto<T> where T: Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let precond = self.precond.to_string();
        let postcond = self.postcond.to_string();
        write!(f, "DTO:\nprecond: {}\npostcond: {}",
               precond, postcond)
    }
}

impl Dto<Lia> {
    fn variable(&self) -> Variable {
        self.grammar[0].sink.clone()
    }

    pub fn to_sygus(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        let header = format!("(synth-fun function (({} Int)) Int\n", self.variable());
        let variables = self.postcond.get_vars();
        let postcond = (*self.postcond)
            .clone()
            .var_to_function(self.variable());
        let quantifier_free = self.precond.is_eq();
        let mut const_vars : HashSet<&Variable> = HashSet::new();

        // If the precond-var is not part of a forall clause
        if quantifier_free {
            for var in &variables {
                const_vars.insert(var);
            }
        }

        // Yes, I know this is repeated
        // Add all variables that aren't part of the function
        for var in &variables {
            if !(var.eq(&self.variable())) {
                const_vars.insert(var);
            }
        }

        for var in const_vars {
            query.push_str(&format!("(declare-const {} Int)\n", var));
        }

        query.push_str(&header);

        query.push_str("\t((I Int))(\n");
        query.push_str("\t\t(I Int (\n");
        for update_term in &*self.grammar {
            query.push_str(&format!("\t\t\t\t{}\n", update_term.to_sygus()));
            query.push_str(&format!("\t\t\t\t{}\n",
                                    update_term
                                    .change_sink_name("I")
                                    .to_sygus()));
        }
        query.push_str("\t\t\t)\n");
        query.push_str("\t\t)\n");
        query.push_str("\t)\n");
        query.push_str(")\n");

        if quantifier_free {
            query.push_str(&self.precond.to_smt2_assert());
            query.push_str(&postcond.to_constraint());
        } else {
            query.push_str(&self.quantified_constraint());
        }
        query.push_str("(check-synth)\n");
        query
    }

    fn synthesize_next(&self, timesteps: u32) -> FunctionLiteral<Lia> {
        let query = self.to_sygus();
        let result = cvc4::runner(&query, "sygus", timesteps);
        cvc4::parse_sygus_result(&result)
    }

    fn quantified_constraint(&self) -> String {
        let mut constraint = format!("(constraint (forall (({} Int))\n", self.variable());
        let postcond = (*self.postcond).clone().
            var_to_function(self.variable());
        constraint.push_str(&format!("\t(=> {}\n", self.precond.to_smtlib()));
        constraint.push_str(&format!("\t{}\n", postcond.to_smtlib()));
        constraint.push_str(")))\n");
        constraint
    }

    // TODO: F
    fn synthesize_eventually(&self) -> FunctionLiteral<Lia> {
        panic!("Not Implemented Error")
    }

    pub fn synthesize(&self) -> FunctionLiteral<Lia> {
        match &self.temporal {
            Temporal::Next(num_next) => self.synthesize_next(num_next.clone()),
            Temporal::Eventually => self.synthesize_eventually()
        }
    }
}
