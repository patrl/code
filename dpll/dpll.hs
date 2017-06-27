{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

import Control.Arrow
import Data.List

data E = A | B | C | D | X deriving (Show, Eq, Enum, Ord)

univ :: [E]
univ = [A .. D]

type Var = Int
type G = Var -> E

type C = [G]
type T = C -> [C]
type U = C -> C

zero :: C
zero = [const X]

modify :: Var -> E -> G -> G
modify v x g = \v' -> if v == v' then x else g v'

instance Show G where
  show = show . flip map [1..5]

instance Show T where
  show p = show $ p zero

instance Show U where
  show p = show $ p zero

(<+>) :: T -> T -> T
(l <+> r) g = [h | i <- l g, h <- r i]

ex :: Var -> U
ex v c = [modify v x g | x <- univ, g <- c]

eq :: E -> E -> U
eq x y c = [g | g <- c, x == y]

lt :: E -> E -> U
lt x y c = [g | g <- c, x < y]

gt :: E -> E -> U
gt x y c = [g | g <- c, x > y]

pro :: Var -> (E -> U) -> U
pro n f c = [h | g <- c, h <- f (g n) [g]]
