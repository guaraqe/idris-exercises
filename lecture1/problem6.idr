import Data.Vect

-- proofs from problem 5
plus_commutes_zero : m = plus m 0
plus_commutes_zero {m = Z} = Refl
plus_commutes_zero {m = (S k)} = let rec = plus_commutes_zero {m=k} in
                                           rewrite sym rec in Refl

plus_commutes_ind : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_ind k Z = Refl
plus_commutes_ind k (S j) = rewrite plus_commutes_ind k j in Refl

-- helper proof for the second case of reverse
plusS : (n : Nat) -> (k : Nat) -> plus (S n) k = plus n (S k)
plusS Z k = Refl
plusS (S j) k = rewrite plus_commutes_ind k j in Refl


vect_reverse : Vect n a -> Vect n a
vect_reverse xs = vect_reverse_acc [] xs where
  vect_reverse_acc : Vect n a -> Vect m a -> Vect (n+m) a
  vect_reverse_acc {n} acc [] = rewrite sym (plus_commutes_zero {m=n})
                                in acc
  vect_reverse_acc {n} {m=S k} acc (x :: xs) = rewrite sym (plusS n k)
                                               in vect_reverse_acc (x :: acc) xs
