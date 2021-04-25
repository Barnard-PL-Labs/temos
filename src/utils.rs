use std::process::Command;
use std::fs;
use rand::Rng;

pub fn run_cvc4(arg: String, lang: &str) -> String {
    let rand_int : i32 = rand::thread_rng().gen();
    let hack_file_name = format!("tmp-hack{}", rand_int);

    fs::write(&hack_file_name, arg).unwrap();
    let output = Command::new("bin/cvc4")
             .arg(&hack_file_name)
             .arg("--lang")
             .arg(lang)
             .output()
             .unwrap();
    fs::remove_file(&hack_file_name).unwrap();

    String::from(String::from_utf8_lossy(&output.stdout).to_string())
}
