use crate::tsl::{PredicateLiteral};
use crate::lia::Lia;

impl PredicateLiteral<Lia> {
    fn evaluate(&self) -> bool {
        panic!("")
    }
    fn to_tsl(&self) -> String {
        String::from("foo")
    }
    pub fn to_tsl_assumption(&self) -> String {
        format!("!{};", self.to_tsl())
    }
}
