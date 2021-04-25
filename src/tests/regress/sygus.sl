(set-logic LIA)
(synth-fun function ((x Int)) Int
	((I Int))(
		(I Int (
				(+ x 1)
				(- x 1)
				x
			)
		)
	)
)
(constraint (= (function 0) 1))
(check-synth)
