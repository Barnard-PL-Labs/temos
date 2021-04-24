(set-logic LIA)
(synth-fun function ((x Int)) Int
	((I Int))(
		(I Int (
				(+ x 1)
				(+ x 2)
				(+ I 1)
				(+ I 2)
			)
		)
	)
)
(constraint (= (function 0) 3))
(check-synth)
