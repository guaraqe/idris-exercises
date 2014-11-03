plus_nSm : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
plus_nSm n m = ?nSm

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z     m = ?commutesZero
plus_commutes (S k) m = ?commutesSucc

plus_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) ->
             n + (m + p) = (n + m) + p
plus_assoc Z     m p = Refl
plus_assoc (S k) m p = ?assoc

---------- Proofs ----------

Main.assoc = proof
  intros
  induction k
  compute
  exact Refl
  intros
  compute
  rewrite ihn__0 
  trivial


Main.commutesSucc = proof
  intros
  rewrite plusSuccRightSucc m k
  induction k
  rewrite sym (commutesZero m)
  compute
  trivial
  intros
  compute
  rewrite sym (plus_nSm m n__0)
  rewrite ihn__0 
  trivial


Main.commutesZero = proof
  intros
  rewrite sym (plusZeroRightNeutral m)
  trivial


Main.nSm = proof
  intros
  rewrite sym (plusSuccRightSucc n m)
  trivial


