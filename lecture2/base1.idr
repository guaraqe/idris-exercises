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

    -- Defines the expressions of our DSL
    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i G t -> Expr G t
        Val : (x : Int) -> Expr G TyInt
        Lam : Expr (a :: G) t -> Expr G (TyFun a t)
        App : Expr G (TyFun a t) -> Expr G a -> Expr G t
        Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c
        If  : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a
    
    -- Write the interpreter for the new language
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
    eId = Lam (Var stop)

    -- Addition, equivalent to using de Bruijn indexes
    eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
    eAdd = Lam (Lam (Op (+) (Var (pop stop)) (Var stop))) 

    -- Double a number, same method
    eDouble : Expr G (TyFun TyInt TyInt)
    eDouble = Lam (App (App eAdd (Var stop)) (Var stop))
   
    (<$>) : Lazy (Expr G (TyFun s t)) -> Lazy (Expr G s) -> Expr G t
    (<$>) x y = App x y

    -- Writing the factorial function
    fact : Expr G (TyFun TyInt TyInt)
    fact = Lam (If (Op (==) (Var stop) (Val 0))
                   (Val 1)
                   (Op (*) (fact <$> (Op (-) (Var stop) (Val 1))) (Var stop)))

-- Test for factorial function         
testFac : Bool
testFac = interp [] fact 4 == 24
