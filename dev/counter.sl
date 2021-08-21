(set-logic LIA)
(declare-const i Int)
(synth-fun function ((x Int)) Int
    ((I Int))
    ((I Int ((+ x i) (- x i)
             ))
    )
)

(assert (and (< 0 i) (< i 5)))
(constraint (forall ((x Int)) 
	(=> 
	(and (<= x 100) (> x 0))
	(and (<= (function x) 100) (>= (function x) 0))
	)))

(check-synth)
