vect_reverse : Vect n a -> Vect n a
vect_reverse [] = []
vect_reverse (x :: xs) ?= (vect_reverse xs) ++ [x]


---------- Proofs ----------

Main.vect_reverse_lemma_1 = proof
  intros
  rewrite plusCommutative n 1
  exact value


