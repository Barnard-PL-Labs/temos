(set-logic LIA)
(synth-fun function ((x Int)) Int
    ((I Int))
    ((I Int ((+ x 1) (- x 1)
             (+ I 1) (- I 1)
             ))
    )
)

(constraint (and (<= (function 0) 100) (>= (function 0) 0)))

(check-synth)
