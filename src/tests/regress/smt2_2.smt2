(set-logic LIA)
(declare-const x Int)
(declare-const y Int)

(assert (< x y))
(check-sat)
