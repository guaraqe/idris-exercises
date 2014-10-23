-- Repeat function
repeat : (n : Nat) -> a -> Vect n a
repeat Z     x = []
repeat (S n) x = x :: repeat n x

-- Type definition
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

-- Vertical concatenation
infixr 10 :^:
(:^:) : Matrix n m a -> Matrix p m a -> Matrix (n+p) m a
(:^:) mat1 mat2 = mat1 ++ mat2

-- Horizontal concatenation
infixr 10 :|:
(:|:) : Matrix n m a -> Matrix n q a -> Matrix n (m+q) a
(:|:) mat1 mat2 = zipWith (++) mat1 mat2

-- Some basic functions for fun, names very explicit
takeFirstLine : Matrix (S n) m a -> Vect m a
takeFirstLine (x::xs) = x

takeFirstColumn : Matrix n (S m) a -> Vect n a
takeFirstColumn mat = map head mat

dropFirstLine : Matrix (S n) m a -> Matrix n m a
dropFirstLine (x::xs) = xs

dropFirstColumn : Matrix n (S m) a -> Matrix n m a
dropFirstColumn mat = map tail mat

addLine : Matrix n m a -> Vect m a -> Matrix (n+1) m a
addLine mat vec = mat ++ [vec]

addColumn : Matrix n m a -> Vect n a -> Matrix n (m+1) a
addColumn mat vec = zipWith add mat vec
    where add : Vect m a -> a -> Vect (m+1) a
          add v e = v ++ [e]

-- Create a column matrix from a vector
vecToColumn : Vect n a -> Matrix n 1 a
vecToColumn []      = []
vecToColumn (x::xs) = [x] :: vecToColumn xs


-- The transpose function
myTranspose : Matrix n m a -> Matrix m n a
myTranspose []      = repeat _ []
myTranspose (l::ls) = (vecToColumn l) :|: transpose ls

-- Vector inner product
infixr 10 :.: 
(:.:) : (Num a) => Vect n a -> Vect n a -> a
(:.:) v1 v2 = sum $ zipWith (*) v1 v2

-- External application function
expWith : (a -> b -> c) -> Vect (S n) a -> Vect (S m) b -> Matrix (S n) (S m) c
expWith f [x] y = map (f x) y :: Nil
expWith f (x::w::xs) y = (map (f x) y) :: expWith f (w::xs) y

-- Matrix multiplication
infixr 10 ><
(><) : (Num a) => Matrix (S n) k a -> Matrix k (S m) a -> Matrix (S n) (S m) a
(><) mat1 mat2 = expWith (:.:) mat1 (myTranspose mat2)

-- Elements for testing
myMatrix : Matrix 3 3 Int
myMatrix = [ [1,2,3]
           , [4,5,6]
           , [7,8,9] ]

myVector : Vect 3 Int
myVector = [10,11,12]

-- Dimension of matrices, for testing
dimV : Vect n a -> Nat
dimV {n} vec = n

dimM : Matrix n m a -> (Nat,Nat)
dimM {n} {m} mat = (n,m)
