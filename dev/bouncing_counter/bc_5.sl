(set-logic LIA)
(synth-fun function ((x Int)) Int
    ((I Int))
    ((I Int ((+ x 1) (- x 1)
             (+ I 1) (- I 1)
             ))
    )
)

(constraint (forall ((x Int)) 
	(=> 
	(and (<= x 100) (> x 0))
	(and (<= (function x) 100) (>= (function x) 0))
	)))

(check-synth)
