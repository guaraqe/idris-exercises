vtake : (n:Nat) -> Vect (n+m) a -> Vect n a
vtake  Z     v      = []
vtake (S k) (x::xs) = x :: vtake k xs

vdrop : (n:Nat) -> Vect (n+m) a -> Vect m a
vdrop  Z     v      = v
vdrop (S k) (x::xs) = vdrop k xs
