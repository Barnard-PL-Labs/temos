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

fn parse_syguslia_result(fxn: String) -> String {
    get_ast(fxn, "Int")
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_assumption() {
        let function = String::from("(define-fun function ((x Int)) Int (+ (+ x 1) 2))");
        let result = parse_syguslia_result(function);
        assert_eq!(&result, "(+ (+ x 1) 2)");
    }
}