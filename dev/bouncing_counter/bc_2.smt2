(set-logic LIA)
(declare-const x Int)

(assert (= x 0))
(assert (= x 100))

(check-sat)
