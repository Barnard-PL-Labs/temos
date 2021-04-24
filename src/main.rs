use Temporal::*;
use Literal::*;
use Predicate::*;
use Update::*;


#[derive(Debug)]
enum Temporal {
    Next(i32),
    Liveness //TODO
}

enum Literal {
    Var(String),
    Const(i32),
}

impl Literal {
    fn to_sygus_str(&self) -> String {
        match self {
            Var(string) => String::from(string),
            Const(val)  => format!("{}", val)
        }
    }
}

enum Update {
    Add(Literal, Literal),
    Sub(Literal, Literal),
    Signal(Literal)
}

impl Update {
    fn to_sygus_str(&self) -> String {
        match self {
            Add(lhs, rhs) => format!("(+ {} {})", 
                                     lhs.to_sygus_str(),
                                     rhs.to_sygus_str()),
            Sub(lhs, rhs) => format!("(- {} {})", 
                                     lhs.to_sygus_str(),
                                     rhs.to_sygus_str()),
            Signal(val) => val.to_sygus_str()
        }
    }
}

enum Predicate {
    LT(Literal, Literal),
    EQ(Literal, Literal)
}

// TODO: readability
impl Predicate {
    // TODO: only use LT? always put var on LHS? etc. ...
    //fn standardize(&self) -> Predicate {
    //}
    fn to_precond(&self) -> String {
        match self {
            EQ(lhs, rhs) =>
                match lhs { 
                    Const(_) => panic!("LHS for EQ has int\n"),
                    Var(_) => format!("(function {})", rhs.to_sygus_str())
                }
            // TODO: forall
            LT(lhs, rhs) => "".to_string()
        }
    }

    // TODO: add logic on panic?? lhs stuff is tricky and/or annoying
    fn to_constraint(&self, precond: &Predicate) -> String {
        let mut constraint_smt = String::from("(constraint ");
        let constraint = match self {
            EQ(_, rhs) => format!("(= {} {})",
                    precond.to_precond(),
                    rhs.to_sygus_str()),
            LT(_, rhs) => format!("(< {} {})",
                    precond.to_precond(),
                    rhs.to_sygus_str()),
        };
        constraint_smt.push_str(&constraint);
        constraint_smt.push_str(")\n");
        constraint_smt }
}

struct SygusHoareTriple {
    precond: Predicate,
    postcond: Predicate,
    var_name: String,
    temporal: Temporal,
    updates: Vec<Update>,
}

impl SygusHoareTriple {
    fn to_sygus(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        let header = format!("(synth-fun function (({} Int)) Int\n", self.var_name);
        query.push_str(&header);
        query.push_str("\t((I Int))(\n");
        query.push_str("\t\t(I Int (\n");
        for update_term in &self.updates {
            query.push_str(&format!("\t\t\t\t{}\n", update_term.to_sygus_str()));
            // TODO: implement (- I 1)
        }
        query.push_str("\t\t\t)\n");
        query.push_str("\t\t)\n");
        query.push_str("\t)\n");
        query.push_str(")\n");
        query.push_str(&self.postcond.to_constraint(&self.precond));
        query.push_str("(check-synth)");
        query
    }

    fn cmd_options(&self) -> String {
        match self.temporal {
            Next(timesteps) => format!("--sygus-abort-size={}", timesteps),
            Liveness => "--shmuel".to_string() // TODO
        }
    }
}

fn main() {
    let updates = vec![Add(Var("x".to_string()), Const(1)),
                       Sub(Var("x".to_string()), Const(1)),
                       Signal(Var("x".to_string()))];
    let hoare = SygusHoareTriple {
        precond  : EQ(Var("x".to_string()), Const(0)),
        postcond : EQ(Var("x".to_string()), Const(1)),
        var_name: "x".to_string(),
        temporal: Next(1),
        updates: updates
    };
    println!("{}", hoare.to_sygus());
    println!("{}", hoare.cmd_options());
}
