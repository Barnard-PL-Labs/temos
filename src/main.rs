mod types; 
mod parser;
mod hoare;
mod predicate;
mod tests;
mod utils;
mod examples;

fn parse_test() {
    let string = "(+ (+ (+ (+ (+ x 1) 1) 1) 1) 1)";
    let stream = parser::scanner(string);
    for tok in &stream {
        print!("{} ", tok.to_tsl());
    }
    println!("\n{}", parser::get_loop_body(stream));
}

fn main() {
    parse_test();
    //examples::examples();
}

 // use regex::Regex;
 // fn main() {
 //     let re = Regex::new(r"^[^\s\(\)]+").unwrap();
 //     let string = "xyz1 2 + )";
 //     let found = re.find(string).unwrap();
 //     println!("{}", &string[found.end()..]); 
 // }
