import Decidable.Equality

data Tree a = Leaf | Node (Tree a) a (Tree a)

data ElemTree : a -> Tree a -> Type where
    Here  : ElemTree x (Node _ x _)
    Left  : ElemTree x node -> ElemTree x (Node node _ _)
    Right : ElemTree x node -> ElemTree x (Node _ _ node) 

elemInTree : DecEq a => (x : a) -> (t : Tree a) -> Maybe (ElemTree x t)
elemInTree x Leaf = Nothing
elemInTree x (Node left y right) with (decEq x y)
                                     | Yes p = rewrite p in Just Here
    elemInTree x (Node left y right) | No _  = case elemInTree x left of
                                                   Nothing => do q <- elemInTree x right
                                                                Just (Right q)
                                                   Just p  => Just (Left p)
