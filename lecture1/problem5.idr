-- `plus_nSm` is covered by `plus_commutes_ind`

plus_commutes_zero : m = plus m 0
plus_commutes_zero {m = Z} = Refl
plus_commutes_zero {m = (S k)} = let rec = plus_commutes_zero {m=k} in
                                     rewrite sym rec in Refl

plus_commutes_ind : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_ind k Z = Refl
plus_commutes_ind k (S j) = rewrite plus_commutes_ind k j in Refl

total
plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z m = plus_commutes_zero
plus_commutes (S k) m = rewrite plus_commutes k m in
                        rewrite plus_commutes_ind k m in Refl

------------------------------------------------------------

total
plus_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc Z m p = Refl
plus_assoc (S k) m p = rewrite plus_assoc k m p in Refl
