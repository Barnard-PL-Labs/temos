pub use Temporal::*;
pub use Literal::*;
pub use Update::*;
pub use Predicate::*;
pub use LogicOp::*;
pub use LiaOp::*;

pub enum Temporal {
    Next(i32),
    Liveness
}

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

pub enum Predicate {
    And(Box<Predicate>, Box<Predicate>),
    Neg(Box<Predicate>),
    Bool(LogicOp, Literal, Literal)
}


// TODO: need standardization, i.e. var always on LHS
impl Predicate {
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

    fn to_assert(&self) -> String {
        let mut smt_str = String::from("(assert ");
        let assertion = match self {
            Bool(op, lhs, rhs) => 
                format!("({} {} {})",
                op.to_string(),
                lhs.to_string(),
                rhs.to_string()),
            _ => panic!("Not Implemented Error")

        };
        smt_str.push_str(&assertion);
        smt_str.push_str(")\n");
        smt_str 
    }

    pub fn to_smt2(&self) -> String {
        let mut query = String::from("(set-logic LIA)\n");
        let mut vars : Vec<&str> = Vec::new();
        match self {
            Bool(_, lhs, rhs) => {
                match lhs {
                    Var(var) => vars.push(&var),
                    _ => ()
                };
                match rhs {
                    Var(var) => vars.push(&var),
                    _ => ()
                }
            },
            _ => panic!("Not Implemented Error")
        };
        for variable in &vars {
            query.push_str(&format!("(declare-const {} Int)\n", variable));
        }
        query.push_str("\n");
        query.push_str(&self.to_assert());
        query.push_str("(check-sat)");
        query
    }

    //pub fn and(&self, pred: &Predicate) -> Predicate {
    //    AND(Box::new(self), Box::new(pred))
    //}
    //pub fn neg(&self) -> Predicate {
    //    NEG(Box::new(self)
    //}
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
        query.push_str("(check-synth)");
        query
    }

    pub fn cmd_options(&self) -> String {
        match self.temporal {
            Next(timesteps) => format!("--sygus-abort-size={}", timesteps),
            Liveness => panic!("Not Implemented Error")
        }
    }
}
