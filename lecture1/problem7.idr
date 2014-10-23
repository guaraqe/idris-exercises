import Decidable.Equality

data Tree a = Leaf | Node (Tree a) a (Tree a)

data ElemTree : a -> Tree a -> Type where
    Here  : ElemTree x (Node _ x _)
    Left  : ElemTree x node -> ElemTree x (Node node _ _)
    Right : ElemTree x node -> ElemTree x (Node _ _ node) 

elemInTree : DecEq a => (x : a) -> (t : Tree a) -> Maybe (ElemTree x t)
elemInTree x Leaf                = Nothing
elemInTree x (Node left y right) with (decEq x y)
    elemInTree x (Node left x right) | Yes _ = ?isHere
    elemInTree x (Node left y right) | No  _ = case elemInTree x left of
                                                  Nothing => do q <- elemInTree x right
                                                                Just (Right q)
                                                  Just p  => Just (Left p)

---------- Proofs ----------

Main.isHere = proof
  intros
  rewrite prf
  exact Just Here


