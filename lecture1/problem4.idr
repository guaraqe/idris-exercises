module MyCMP

data MyCmp : Nat -> Nat -> Type where
    myCmpLT : (y : _) -> MyCmp x (x + S y)
    myCmpEQ : MyCmp x x
    myCmpGT : (x : _) -> MyCmp (y + S x) y


total
myCmp : (n : Nat) -> (m : Nat) -> MyCmp n m
myCmp Z     Z     = myCmpEQ {x = Z}
myCmp Z     (S k) = myCmpLT k
myCmp (S k) Z     = myCmpGT k
myCmp (S k) (S l) with (myCmp k l)
    myCmp (S k) (S k)         | myCmpEQ   = myCmpEQ {x = S k}
    myCmp (S k) (S (k + S j)) | myCmpLT j = myCmpLT j
    myCmp (S (l + S j)) (S l) | myCmpGT j = myCmpGT j

