import Data.Vect

repeat : (n : Nat) -> a -> Vect n a
repeat Z a = []
repeat (S n) a = a :: repeat n a
