use std::process::Command;
use std::fs;
use rand::Rng;
use std::time::{Duration, Instant};
use crate::types::*;
use crate::parser;

// TODO: timer interrupt

pub fn cvc4_generic(arg: String, lang: &str) -> String {
    let rand_int : i32 = rand::thread_rng().gen();  // XXX
    let hack_file_name = format!("tmp-hack{}", rand_int);

    fs::write(&hack_file_name, &arg).unwrap();
    let output = Command::new("bin/cvc4")
        .arg(&hack_file_name)
        .arg("--lang")
        .arg(lang)
        .output()
        .unwrap();
    fs::remove_file(&hack_file_name).unwrap();

    let err = String::from_utf8_lossy(&output.stderr);
    if !err.eq("") {
        println!("CVC4 Error:\n{}\n{}", err, arg);
    }
    String::from(String::from_utf8_lossy(&output.stdout).to_string())
}

// XXX: combine into one function...
pub fn sygus_cvc4(arg: String, lang: &str, abort_size: u32) -> String {
    let rand_int : i32 = rand::thread_rng().gen();
    let hack_file_name = format!("tmp-hack{}", rand_int);
    let max_abort_size = format!("--sygus-abort-size={}", abort_size);

    fs::write(&hack_file_name, &arg).unwrap();
    let output = Command::new("bin/cvc4")
        .arg(&hack_file_name)
        .arg("--lang")
        .arg(lang)
        .arg(max_abort_size)
        .output()
        .unwrap();
    fs::remove_file(&hack_file_name).unwrap();

    let err = String::from_utf8_lossy(&output.stderr);
    if !err.eq("") {
        println!("CVC4 Error:\n{}\n{}", err, arg);
    }
    String::from(String::from_utf8_lossy(&output.stdout).to_string())
}

pub fn tsltools(path: &str) -> &str {
    let output = Command::new("bin/tsl2js.sh")
        .arg(path)
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&output.stderr);
    print!("{}", (String::from_utf8_lossy(&output.stdout)));
    if err.eq("UNREALIZABLE\n") {
        return "UNREALIZABLE";
    }
    if !err.eq("") {
        panic!("***ERROR!***{:?}", err)
    }
    "REALIZABLE"
}

pub fn time_tsl_synth(path: &str) -> (String, Duration) {
    let before = Instant::now();
    (tsltools(path).to_string(),
    Instant::now().duration_since(before))
}

pub fn time_tsllia(spec: Specification) -> (String, Duration) {
    let before = Instant::now();
    (spec.to_always_assume(), Instant::now().duration_since(before))
}

pub fn time_final_tsl(assumptions: &str, tsl_path: &str) -> (String, Duration) {
    let rand_int : i32 = rand::thread_rng().gen();
    let hack_file_name = format!("tmp-hack{}.tsl", rand_int);

    let tsl = fs::read_to_string(tsl_path).unwrap();
    let final_tsl = [assumptions, &tsl].join("\n");

    fs::write(&hack_file_name, &final_tsl).unwrap();
    let result = time_tsl_synth(&hack_file_name);
    return result;
}

pub fn time_all(json_path: &str, tsl_path: &str) -> (Duration, Duration) {
    let lia_spec = parser::json::get_spec_from_json(&json_path);
    let (ass, lia_dur) = time_tsllia(lia_spec);
    let (is_realizable, tsl_dur) = time_final_tsl(&ass, tsl_path);
    println!("{}", is_realizable);
    (lia_dur, tsl_dur)
}
