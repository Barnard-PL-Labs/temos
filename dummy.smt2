(set-logic LIA)
(declare-const x Int)

(assert (and (< x 5) (not (= x 4))))
(check-sat)
