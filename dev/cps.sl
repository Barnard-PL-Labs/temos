(set-logic LRA)
;;(declare-const x1 Real)
;;(declare-const x2 Real)

(synth-fun fx1 ((x Real)) Real
    ((I Real))
    ((I Real ((+ x 0) (+ x 0.09740)
             (+ I 0.09740) 
             ))
    )
)

(synth-fun fx2 ((x Real)) Real
    ((I Real))
    ((I Real ((* x 0.9635)
             (+ I 0.9635) 
             ))
    )
)

;;(constraint (forall ((x Real)) 
;;	(=> 
;;	(and (<= 0.1 x) (< 0.2 x))
;;	(and (<= (fx1 x) 0.7) (>= (fx1 x) 0.1))
;;	)))
;;
;;(constraint (forall ((x Real)) 
;;	(=> 
;;	(and (<= 0.1 x) (< 0.2 x))
;;	(and (<= (fx2 x) 0.7) (>= (fx2 x) 0.1))
;;	)))

(constraint (forall ((x1 Real)(x2 Real)) 
	(=> 
	(and (and (<= 0.1 x1) (< 0.2 x1)) (and (<= 0.1 x2) (< 0.2 x2)))
	(or (>= (fx1 x1) 0.2)(>= (fx2 x2) 0.2))
)))

(check-synth)
