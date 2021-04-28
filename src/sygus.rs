// Horrible, horrible function
fn get_ast(fxn: String, keyword: &str) -> String {
    let kw_indices: Vec<_> = fxn.match_indices(keyword).collect();
    let paren_indices: Vec<_> = fxn.match_indices("(").collect();
    let last_kw = kw_indices.last()
                          .expect(&format!("bad sygus result: {}.\n
                                           no instance of {}", fxn, keyword))
                          .0;
    let mut paren_idx = 0;
    for (idx, _) in paren_indices {
        if last_kw < idx {
            paren_idx = idx;
            break;
        }
    }
    if paren_idx == 0 {
        panic!("Can't find parentheses!");
    }
    String::from(&fxn[paren_idx..fxn.chars().count()-1])
}

// TODO
pub fn fxn_to_tsl(sygus_result: String) -> String {
    // let fxn = get_ast(sygus_result, "Int");
    sygus_result
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
