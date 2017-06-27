data Var = X | Y | Z deriving (Show, Eq)

data Form = Eq Var Var | Gt Var Var | Lt Var Var
          | Neg Form | Conj Form Form | Ex Var Form | Hm Var Form
  deriving (Show, Eq)

type Assignment = Var -> Int

modify :: Var -> Int -> Assignment -> Assignment
modify var x g = \var' -> if var == var' then x else g var'

modify' :: Var -> Int -> Assignment -> Assignment
modify' var x g = \var' -> if var == var' && x > g var' then x else g var'

domain :: [Int]
domain = [1..10]

eval :: Form -> Assignment -> Bool
eval (Eq x y)   = \g -> g x == g y
eval (Gt x y)   = \g -> g x > g y
eval (Lt x y)   = \g -> g x < g y
eval (Neg p)    = \g -> not (eval p g)
eval (Conj p q) = \g -> eval p g && eval q g
eval (Ex x p)   = \g -> any (\x' -> eval p $ modify  x x' g) domain
eval (Hm x p)   = \g -> any (\x' -> eval p $ modify' x x' g) domain

evalD :: Form -> Assignment -> [Int]
evalD = undefined
