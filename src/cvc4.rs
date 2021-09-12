use rand::Rng;
use std::process::Command;
use std::fs;

/// Runs CVC4 by creating a temp file and feeding it into CVC4.
pub fn cvc4_runner(arg: &str, lang: &str, abort_size: u32) -> String {
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
