use serde_json;
use serde::{Deserialize, Serialize};
use std::fs;
use crate::types::*;


fn str_to_literal(s: &str) -> Literal {
    match s.parse::<i32>() {
        Ok(int) => Const(int),
        Err(_) => Var(s.to_string())
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct JsonPredicate {
    pred: String,
    temporal: Vec<String>
}

impl JsonPredicate {
    fn to_spec_predicate(self) -> SpecPredicate {
        SpecPredicate {
            pred: JsonPredicate::str_to_predicate(&self.pred),
            temporal: self.temporal
                .into_iter()
                .map(|x| JsonPredicate::str_to_temporal(&x))
                .collect()
        }
    }

    fn str_to_temporal(string: &str) -> Temporal {
        match string {
            "X" => Next(1),
            "F" => Liveness,
            _ => panic!("Not yet supported")
        }
    }

    fn str_to_predicate(string: &str) -> Predicate {
        let terms : Vec<&str> = string
            .split_whitespace()
            .collect();
        if terms.len() == 7 {
            let op = match terms[0] {
               "and" => Predicate::new_and,
               _ => panic!("Unexpected operator")
            };
            return op(JsonPredicate::str_to_predicate(&terms[1..4].join(" ")),
            JsonPredicate::str_to_predicate(&terms[4..].join(" ")));
        }
        if terms.len() != 3 {
            panic!("Unexpected predicate json, {}", string);
        }
        let operator = match terms[0] { 
            "lt" => LT,
            "gt" => GT,
            "eq" => EQ,
            "lte" => LTE,
            "gte" => GTE,
            _ => panic!("Unexpected operator")
        };
        let lhs = str_to_literal(terms[1]);
        let rhs = str_to_literal(terms[2]);
        Bool(operator, lhs, rhs)
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct JsonUpdate {
    update_term: String,
    var_name: String,
    depends: Vec<String>
}

impl JsonUpdate {
    fn to_update(self) -> Update {
        Update {
            update_term: JsonUpdate::str_to_update_term(&self.update_term),
            var_name: self.var_name,
            depends: self.depends
        }
    }

    fn str_to_update_term(string: &str) -> UpdateTerm {
        let terms : Vec<&str> = string
            .split_whitespace()
            .collect();
        if terms.len() == 1 {
            return Signal(str_to_literal(terms[0]));
        }
        else if terms.len() == 3 {
            let lia_op = match terms[0] {
                "add" => Add,
                "sub" => Sub,
                _ => panic!("Unsupported LIA operator")
            };
            let lhs = str_to_literal(terms[1]);
            let rhs = str_to_literal(terms[2]); 
            return Function(lia_op, lhs, rhs);
        }
        else {
            panic!("Unexpected length of terms");
        }
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct JsonSpecification {
    predicates: Vec<JsonPredicate>,
    updates: Vec<JsonUpdate>
}

impl JsonSpecification {
    fn to_specification(self) -> Specification {
        Specification {
            predicates: self.predicates
                .into_iter()
                .map(|x| x.to_spec_predicate())
                .collect(),
            updates: self.updates
                .into_iter()
                .map(|x| x.to_update())
                .collect()
        }
    }
}

pub fn get_spec_from_json(path: &str) -> Specification {
    let data = fs::read_to_string(path).unwrap();
    let res: JsonSpecification = serde_json::from_str(&data).expect("Unable to parse\n");
    res.to_specification()
}
