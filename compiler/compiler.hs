data Expr = Val Int | Add Expr Expr | Sub Expr Expr

data Code = HALT | PUSH Int Code | ADD Code | SUB Code
            deriving (Show, Eq)

comp :: Expr -> Code
comp e = comp' e HALT

comp' :: Expr -> Code -> Code
comp' (Val n)   c = PUSH n c
comp' (Add x y) c = comp' x (comp' y (ADD c))
comp' (Sub x y) c = comp' x (comp' y (SUB c))

type Stack = [Int]

exec :: Code -> Stack -> Stack
exec HALT       s           = s
exec (PUSH n c) s           = exec c (n : s)
exec (ADD c)    (m : n : s) = exec c (n+m : s)
exec (SUB c)    (m : n : s) = exec c (n-m : s)

eval :: Expr -> Int
eval exp = head $ (exec . comp) exp []

