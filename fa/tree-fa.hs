infixr 5 :->
data Type = E | T | Type :-> Type deriving Eq

instance Show Type where
  show E = "e"
  show T = "t"
  show (m@(a :-> b) :-> c) = "("++ show m ++")" ++" -> "++ show c
  show (a :-> b) = show a ++" -> "++ show b

data Tree = Leaf String | Bin Tree Tree deriving (Show, Eq)
type Sem = String
data ParseTree = Nil | App Sem Type ParseTree ParseTree deriving (Show, Eq)

lexicon :: String -> Type
lexicon w
  | w == "John" || w == "Mary" = E
  | w == "left"                = E :-> T
  | w == "saw"                 = E :-> E :-> T
  | w == "gave"                = E :-> E :-> E :-> T
  | w == "everyone"            = (E :-> T) :-> T
  | w == "every"               = (E :-> T) :-> (E :-> T) :-> T
  | w == "the"                 = (E :-> T) :-> E
  | w == "big"                 = E :-> T
  | w == "boy"                 = E :-> T

source :: Type -> Type
source (a :-> _) = a
source a         = a

target :: Type -> Type
target (_ :-> b) = b
target b         = b

rightmost :: Type -> Type
rightmost (_ :-> a) = rightmost a
rightmost a         = a

combine :: Tree -> ParseTree
combine (Leaf w)    = App ("["++ w ++"]") (lexicon w) Nil Nil
combine (Bin t1 t2) = unifyType t1' t2' t1' t2'
  where t1' = combine t1
        t2' = combine t2

unifyType :: ParseTree -> ParseTree -> ParseTree -> ParseTree -> ParseTree
unifyType (App v1 t1 _ _) (App v2 t2 _ _)
  | t1 == source t2 = App ("("++ v2 ++ v1 ++")") $ target t2
  | source t1 == t2 = App ("("++ v1 ++ v2 ++")") $ target t1
  | t1 == t2 && rightmost t1 == T = App ("("++ v1 ++"&"++ v2 ++")") $ t1
  | otherwise = error "types don't match"

main = putStrLn . show . combine $ Bin (Bin (Leaf "every") (Bin (Leaf "big") (Leaf "boy"))) (Bin (Leaf "saw") (Bin (Leaf "the") (Bin (Leaf "big") (Leaf "boy"))))
