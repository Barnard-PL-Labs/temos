(set-logic LIA)
(declare-const x Int)

(assert (= x 0))
(assert (not (and (<= x 100) (>= x 0))))

(check-sat)
