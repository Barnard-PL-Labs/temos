#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Predicate {
    BinaryPredicate(BinaryPredicate),
    Connective(Connective)
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
enum Connective {
    And,
    Neg
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
enum BinaryPredicate {
    LT,
    GT,
    EQ,
    LTE,
    GTE
}

impl BinaryPredicate {
    fn to_string(&self) -> String {
        match self {
            LT  => String::from("<"),
            GT  => String::from(">"),
            EQ  => String::from("="),
            LTE => String::from("<="),
            GTE => String::from(">=")
        }
    }
    fn to_tsl(&self) -> String {
        match self {
            LT  => String::from("lt"),
            GT  => String::from("gt"),
            EQ  => String::from("eq"),
            LTE => String::from("lte"),
            GTE => String::from("gte")
        }
    }
    fn reverse(&self) -> BinaryPredicate {
        match self {
            LT  => BinaryPredicate::GTE,
            GT  => BinaryPredicate::LTE,
            LTE => BinaryPredicate::GT,
            GTE => BinaryPredicate::LT,
            EQ  => panic!("No reversal for EQ")
        }
    }
    fn is_lt(&self) -> bool {
        match self {
            LT  => true,
            LTE => true,
            _   => false
        }
    }
    fn is_gt(&self) -> bool {
        match self {
            GT  => true,
            GTE => true,
            _   => false
        }
    }
}
