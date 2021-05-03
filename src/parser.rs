use crate::types::*;
use Token::*;
use regex::Regex;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Token {
    Lparen,
    Rparen,
    Plus,
    Minus,
    Number(i32),
    Variable(String)
}

impl Token {
    pub fn to_tsl(&self) -> String {
        match self {
            Lparen => "(".to_string(),
            Rparen => ")".to_string(),
            Plus => "add".to_string(),
            Minus => "sub".to_string(),
            Number(val) => val.to_string(),
            Variable(var) => var.to_string()
        }
    }
}
  
// Horrible, horrible function
fn get_ast(fxn: String, keyword: &str) -> String {
    let kw_indices: Vec<_> = fxn.match_indices(keyword).collect();
    let last_kw = kw_indices.last()
        .expect(&format!("bad sygus result: {}.\n
                                           no instance of {}", fxn, keyword))
        .0;
    let start = last_kw + keyword.chars().count() + 1;
    let end = fxn.chars().count()-1;
    String::from(&fxn[start..end])
}

pub fn scanner(sygus_result: &str) -> Vec<Token> {
    let mut sygus_result = sygus_result.to_string();
    let mut stream_of_tokens : Vec<Token> = Vec::new();
    let lparen = Regex::new(r"^\(").unwrap();
    let rparen = Regex::new(r"^\)").unwrap();
    let plus = Regex::new(r"^\+").unwrap();
    let minus = Regex::new(r"^\-").unwrap();
    let whitespace = Regex::new(r"^\s").unwrap();
    let number = Regex::new(r"^[0-9\.]+").unwrap();
    let variable = Regex::new(r"^[^\s\(\)]+").unwrap();
    while !sygus_result.eq("") {
        if lparen.is_match(&sygus_result) {
            stream_of_tokens.push(Lparen);
            sygus_result = sygus_result[1..].to_string();
        }
        else if rparen.is_match(&sygus_result) {
            stream_of_tokens.push(Rparen);
            sygus_result = sygus_result[1..].to_string();
        }
        else if plus.is_match(&sygus_result) {
            stream_of_tokens.push(Plus);
            sygus_result = sygus_result[1..].to_string();
        }
        else if minus.is_match(&sygus_result) {
            stream_of_tokens.push(Minus);
            sygus_result = sygus_result[1..].to_string();
        }
        else if whitespace.is_match(&sygus_result) {
            sygus_result = sygus_result[1..].to_string();
        }
        else if number.is_match(&sygus_result) {
            let re_match = number.find(&sygus_result).unwrap();
            let numeral: i32 = sygus_result[re_match.start()..re_match.end()].parse().unwrap();
            stream_of_tokens.push(Number(numeral));
            sygus_result = sygus_result[re_match.end()..].to_string();
        }
        else if variable.is_match(&sygus_result) {
            let re_match = variable.find(&sygus_result).unwrap();
            let var_name = sygus_result[re_match.start()..re_match.end()].to_string();
            stream_of_tokens.push(Variable(var_name));
            sygus_result = sygus_result[re_match.end()..].to_string();
        }
    }
    stream_of_tokens
}

fn get_variable(stream: &Vec<Token>) -> String {
    for token in stream {
        match token {
            Variable(var) => {
                return var.to_string()
            }
                _ => continue
        }
    };
    panic!("No variable in stream of tokens!\n")
}

pub fn get_loop_body(stream: Vec<Token>) -> String {
    let n : usize = stream.len();
    let operator;
    let variable;
    let argument;

    if n < 3 {
        panic!("AST is too short!\n{:?}", stream)
    }
    if stream[0] != Lparen || stream[n-1] != Rparen {
        panic!("Not a valid AST!\n")
    }
    if stream[1] != Plus && stream[1] != Minus {
        panic!("Invalid function: found {:?} for \n{:?}",
               stream[1], stream)
    }

    operator = stream[1].to_tsl();
    variable = get_variable(&stream);
    argument = stream[n-2].to_tsl();

    format!("({} {} {})",
    operator, variable, argument)
}

pub fn fxn_to_tsl(sygus_result: String) -> String {
    let ast_str = get_ast(sygus_result, "Int");
    let stream_of_tok = scanner(&ast_str);
    let str_of_tok: Vec<String> = stream_of_tok
        .iter()
        .map(|x| x.to_tsl())
        .collect();
    str_of_tok.join(" ")
}

/// Returns None when result is unrealizable.
pub fn get_sygus_result(result: &str) -> Option<String> {
    let mut lines = result.lines();
    if lines.next().unwrap().eq("unsat") {
        Some(String::from(lines.next().unwrap()))
    } else {
        None
    }
}

pub fn get_while_loop(sygus_results: Vec<String>) -> String {
    let bodies: Vec<String> = sygus_results.iter()
        .map(|x| get_loop_body(scanner(&x)))
        .collect();
    let all_same = bodies.iter().all(|x| x == &bodies[0]);
    if !all_same {
        panic!("Obtaining loop body failed.\n");
    }
    bodies[0].clone()
}

pub fn parse_model(cvc4_result: &str) -> String {
    let mut lines = cvc4_result.lines();
    if lines.next().unwrap().eq("sat") {
        if !lines.next().unwrap().eq("(") {
            panic!(format!("Invalid Model result!\n{}", cvc4_result))
        }
        get_ast(lines.next().unwrap().to_string(), "Int")
    } else {
        panic!("Couldn't get model for forall!\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_assumption() {
        let function = String::from("(define-fun function ((x Int)) Int (+ (+ x 1) 2))");
        let result = fxn_to_tsl(function);
        assert_eq!(&result, "(+ (+ x 1) 2)");
    }
}
