-- Define basic data types: Int, Bool and Functions
data Ty = TyInt
        | TyBool
        | TyFun Ty Ty

-- Translate from the DSL to the Meta-Language
interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect n Ty)
    
    -- Define the environment as a vector of types
    data Env : Vect n Ty -> Type where
         Nil  : Env Nil
         (::) : interpTy a -> Env G -> Env (a :: G)
    
    -- Affirmation of type and a proof of this affirmation
    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
         stop : HasType FZ (t :: G) t
         pop  : HasType k G t -> HasType (FS k) (u :: G) t
    
    -- Lookup element in the environment
    lookup : HasType i G t -> Env G -> interpTy t
    lookup stop    (x :: xs) = x
    lookup (pop k) (x :: xs) = lookup k xs

    -- Defines the kinds of our dsl
    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i G t -> Expr G t
        Val : (x : Int) -> Expr G TyInt
        Lam : Expr (a :: G) t -> Expr G (TyFun a t)
        App : Expr G (TyFun a t) -> Expr G a -> Expr G t
        Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c
        If  : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a

    -- Syntax overloading for the dsl
    dsl expr
        lambda      = Lam
        variable    = Var
        index_first = stop
        index_next  = pop
   
    -- Lazy function application
    (<$>) : Lazy (Expr G (TyFun s t)) -> Lazy (Expr G s) -> Expr G t
    (<$>) x y = App x y

    -- Indentity
    pure : Expr G a -> Expr G a
    pure = id

    -- Syntax for if clauses
    syntax IF [x] THEN [t] ELSE [e] = If x t e

    -- Syntax for equality
    (==) : Expr G TyInt -> Expr G TyInt -> Expr G TyBool
    (==) = Op (==)

    -- Syntax for comparison
    (<) : Expr G TyInt -> Expr G TyInt -> Expr G TyBool
    (<) = Op (<)

    -- Make dsl Ints part of the Num class
    instance Num (Expr G TyInt) where
        (+) x y = Op (+) x y
        (-) x y = Op (-) x y
        (*) x y = Op (*) x y
        abs x = IF x < 0 THEN (0-x) ELSE x
        fromInteger = Val . fromInteger

    -- Write the interpreter given the new syntax
    total
    interp : Env G -> Expr G t -> interpTy t
    interp env (Var i)     = lookup i env
    interp env (Val x)     = x
    interp env (Lam sc)    = \x => interp (x :: env) sc
    interp env (App f s)   = interp env f (interp env s)
    interp env (Op op x y) = op (interp env x) (interp env y)
    interp env (If x t e)  = if interp env x then interp env t
                                             else interp env e

    -- Int -> Int : \x => x
    eId : Expr G (TyFun TyInt TyInt)
    eId = expr (\x => x)

    -- Addition, equivalent to using de Bruijn indexes
    eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
    eAdd = expr (\x, y => x + y)

    -- Double a number, same method
    eDouble : Expr G (TyFun TyInt TyInt)
    eDouble = expr (\x => x + x)
    
    -- Writing the factorial function
    fact : Expr G (TyFun TyInt TyInt)
    fact = expr (\x => IF x == 0 THEN 1 ELSE [| fact (x-1) |] * x)
               
-- Test for factorial function   
testFac : Bool
testFac = interp [] fact 4 == 24

main : IO ()
main = do putStr "Enter a number: "
          n <- getLine
          putStrLn ("Answer: " ++ show (interp [] fact (cast n)))
