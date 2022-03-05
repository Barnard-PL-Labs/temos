(set-logic LIA)
(set-option :produce-models true)
(declare-const loc Int)

(assert (and (<= loc 1) (<= 0 loc)))
(check-sat)
(get-model)
