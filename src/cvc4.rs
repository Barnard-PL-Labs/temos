use rand::Rng;
use std::process::Command;
use std::fs;
use crate::tsl::{FunctionLiteral, Theory};

/// Runs CVC4 by creating a temp file and feeding it into CVC4.
pub fn runner(arg: &str, lang: &str, abort_size: u32) -> String {
    let rand_int : i32 = rand::thread_rng().gen();
    let hack_file_name = format!("tmp-hack{}", rand_int);
    let max_abort_size = format!("--sygus-abort-size={}", abort_size);

    fs::write(&hack_file_name, &arg).unwrap();
    let output = match lang {
        "sygus" => Command::new("bin/cvc4")
            .arg(&hack_file_name)
            .arg("--lang")
            .arg(lang)
            .arg(max_abort_size)
            .output()
            .unwrap(),
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

// TODO
pub fn parse_sygus_result<T: Theory>(result: &str, query: &str)
-> FunctionLiteral<T> {
    panic!("Failed to parse result.\n
           Result:\n{}\n
           Query:\n{}\n", result, query)
}
