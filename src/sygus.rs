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

// TODO
pub fn fxn_to_tsl(sygus_result: String) -> String {
    // let fxn = get_ast(sygus_result, "Int");
    // println!("FUNCTION: {}", &fxn);
    // fxn
    format!("[{}]", get_ast(sygus_result, "Int"))
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
