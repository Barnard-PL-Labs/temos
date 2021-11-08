use std::fs;
use rand::Rng;
use std::process::Command;
use regex::Regex;
use crate::tsl::{Funct, FunctionLiteral, LogicWritable, Variable, TheoryFunctions};
use crate::theories::lia::{Lia, Function, Literal, BinaryFunction};

/// Runs CVC4 by creating a temp file and feeding it into CVC4.
pub fn runner(arg: &str, lang: &str, abort_size: u32) -> String {
    let rand_int : i32 = rand::thread_rng().gen();
    let hack_file_name = format!("tmp-hack{}", rand_int);

    fs::write(&hack_file_name, &arg).unwrap();
    let output = match lang {
        "sygus" => {
            if 0 < abort_size {
                let max_abort_size = format!("--sygus-abort-size={}",
                                             abort_size);
                Command::new("bin/cvc4")
                    .arg(&hack_file_name)
                    .arg("--lang")
                    .arg("sygus2")
                    .arg(max_abort_size)
                    .output()
                    .unwrap()
            } else {
                Command::new("bin/cvc4")
                    .arg(&hack_file_name)
                    .arg("--lang")
                    .arg("sygus2")
                    .output()
                    .unwrap()
            }
        },
        "smt" => Command::new("bin/cvc4")
        .arg(&hack_file_name)
        .arg("--lang")
        .arg(lang)
        .output()
        .unwrap(),
        _ => panic!("Invalid language to CVC4: {}", lang)
    };
    fs::remove_file(&hack_file_name).unwrap();

    let err = String::from_utf8_lossy(&output.stderr);
    if !err.eq("") {
        println!("CVC4 Error:\n{}\n{}", err, arg);
    }
    String::from(String::from_utf8_lossy(&output.stdout).to_string())
}

pub fn parse_satisfiable(result: &str, query: &str) -> bool {
        if result == "sat\n" {
            return true
        } else if result == "unsat\n" {
            return false
        } else {
            panic!("Not sat or unsat??\n
                   Result:{}\nQuery:\n{}",
                   result, query);
        }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Token {
    Lparen,
    Rparen,
    Plus,
    Minus,
    Number(i32),
    Variable(String)
}

impl LogicWritable for Token {
    fn to_smtlib(&self) -> String {
        match self {
            Token::Lparen => "(".to_string(),
            Token::Rparen => ")".to_string(),
            Token::Plus => "+".to_string(),
            Token::Minus => "-".to_string(),
            Token::Number(val) => val.to_string(),
            Token::Variable(var) => var.to_string()
        }
    }
    fn to_tsl(&self) -> String {
        match self {
            Token::Lparen => "(".to_string(),
            Token::Rparen => ")".to_string(),
            Token::Plus => "add".to_string(),
            Token::Minus => "sub".to_string(),
            Token::Number(val) => format!("c{}()", val),
            Token::Variable(var) => var.to_string()
        }
    }
}

impl Token {
    pub fn to_function(self) -> TheoryFunctions<Lia> {
        let function = match self {
            Token::Number(num) => Function::NullaryFunction(
                Literal::Const(num)
            ),
            Token::Variable(var) => Function::NullaryFunction(
                Literal::Var(Variable::Variable(var))
            ),
            Token::Plus => Function::BinaryFunction(
                BinaryFunction::Add
            ),
            Token::Minus => Function::BinaryFunction(
                BinaryFunction::Sub
            ),
            _ => panic!("{:?} can't be function", self)
        };
        TheoryFunctions::Function(function)
    }
    pub fn to_nullary_function_literal(self) -> FunctionLiteral<Lia> {
        let function = self.to_function();
        FunctionLiteral::new(
            Lia::LIA,
            function,
            vec![]
        )
    }
}


pub fn scan(sygus_result: &str) -> Vec<Token> {
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
            stream_of_tokens.push(Token::Lparen);
            sygus_result = sygus_result[1..].to_string();
        }
        else if rparen.is_match(&sygus_result) {
            stream_of_tokens.push(Token::Rparen);
            sygus_result = sygus_result[1..].to_string();
        }
        else if plus.is_match(&sygus_result) {
            stream_of_tokens.push(Token::Plus);
            sygus_result = sygus_result[1..].to_string();
        }
        else if minus.is_match(&sygus_result) {
            stream_of_tokens.push(Token::Minus);
            sygus_result = sygus_result[1..].to_string();
        }
        else if whitespace.is_match(&sygus_result) {
            sygus_result = sygus_result[1..].to_string();
        }
        else if number.is_match(&sygus_result) {
            let re_match = number.find(&sygus_result).unwrap();
            let numeral: i32 = sygus_result[re_match.start()..re_match.end()]
                .parse()
                .unwrap();
            stream_of_tokens.push(Token::Number(numeral));
            sygus_result = sygus_result[re_match.end()..].to_string();
        }
        else if variable.is_match(&sygus_result) {
            let re_match = variable.find(&sygus_result).unwrap();
            let var_name = sygus_result[re_match.start()..re_match.end()].to_string();
            stream_of_tokens.push(Token::Variable(var_name));
            sygus_result = sygus_result[re_match.end()..].to_string();
        }
    }
    stream_of_tokens
}

fn parse(tokens: &[Token]) -> FunctionLiteral<Lia> {
    println!("tokens: {:?}", tokens);
    fn matching_rparen_idx(tokens: &[Token], lparen_idx: usize) -> usize {
        let mut balance: i32 = 0;
        let mut token_idx = lparen_idx;
        while token_idx < tokens.len() {
            match tokens[token_idx] {
                Token::Lparen => {balance += 1;}
                Token::Rparen => {balance -= 1;}
                _ => ()
            }
            if balance == 0 {
                return token_idx;
            } else if balance < 0 {
                panic!("Too many rparens!\n{:?}", tokens)
            }
            token_idx += 1;
        }
        panic!("Too many lparens!\n{:?}", tokens)
    }
    let function_idx = 0;
    let function = tokens[function_idx]
        .clone()
        .to_function();
    let theory = Lia::LIA;
    let mut args = Vec::new();

    let mut token_idx = function_idx + 1;
    while token_idx < tokens.len() {
        let token = &tokens[token_idx];
        let function_literal = match token {
            Token::Lparen => {
                let lparen_idx = token_idx.clone();
                let rparen_idx = matching_rparen_idx(&tokens, lparen_idx.clone());
                token_idx = rparen_idx;
                parse(&tokens[lparen_idx+1..rparen_idx])
            },
            Token::Number(_) => token.clone().to_nullary_function_literal(),
            Token::Variable(_) => token.clone().to_nullary_function_literal(),
            _ => panic!("Invalid token during parsing!\n{:?}", token)
        };
        args.push(function_literal);
        token_idx += 1;
    }

    // Validate arity
    if function.arity() != args.len() as u32 {
        panic!("Arity Mismatch!\n
               Function:{}\n
               Tokens:{:?}", function, tokens)
    }

    FunctionLiteral::new(
        theory,
        function,
        args
    )
}


// Horrible, horrible function
fn get_function(sygus_result: &str, keyword: &str) -> String {
    let kw_indices: Vec<_> = sygus_result.match_indices(keyword).collect();
    let last_kw = kw_indices.last()
        .expect(&format!("bad sygus result: {}.\n
                         no instance of {}", sygus_result, keyword))
        .0;
    let start = last_kw + keyword.chars().count() + 2;
    let end = sygus_result.chars().count() - 2;
    String::from(&sygus_result[start..end])
}

// TODO: parse
pub fn parse_sygus_result(result: &str) -> FunctionLiteral<Lia> {
    parse(&scan(&get_function(result, "Int")))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_get_function() {
        let function = "(define-fun function ((x Int)) Int (+ (+ x 1) 2))";
        let result = get_function(function, "Int");
        assert_eq!(&result, "+ (+ x 1) 2");
    }
}
