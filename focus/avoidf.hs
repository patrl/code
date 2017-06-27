-- details here http://tiny.cc/avoidf

{-# LANGUAGE FlexibleInstances #-}

module Main (main) where

type E = String
type T = String
data F a = F a [a] deriving (Show, Eq)

domain :: [E]
domain = ["Bill", "Mary", "Sue", "John"]

instance Functor F where
  fmap k (F x xs) = F (k x) $ map k xs

pamf :: F a -> (a -> b) -> F b
pamf = flip fmap

foc :: E -> F E
foc x = F x domain

saw :: (E, E) -> T
saw (x, y) = x ++ " saw " ++ y

class Contrast f where
  contrast :: T -> f -> Bool
  point :: f -> T
  propAlts :: f -> [T]

instance Contrast (F T) where
  contrast c (F x xs) = any (\y -> y == c && y /= x) xs
  point (F x xs) = x
  propAlts (F x xs) = [y | y <- xs, y /= x]

instance {-# OVERLAPS #-} (Eq a, Contrast a) => Contrast (F a) where
  contrast c (F x xs) = any (\y -> contrast c y && y /= x) xs
  point (F x xs) = point x
  propAlts (F x xs) = concatMap propAlts [y | y <- xs, y /= x]

ant :: T
ant = saw ("John", "Mary")  -- John saw Mary

s0 = foc "Bill" `pamf`
  \x -> saw (x, "Mary")     -- BILL saw Mary
s1 = foc "Mary" `pamf`
  \x -> saw ("Bill", x)     -- Bill saw MARY
s2 = foc "Bill" `pamf`
  \x -> foc "Mary" `pamf`
    \y -> saw (x, y)        -- BILL saw MARY (SS)
s3 = foc "Mary" `pamf`
  \y -> foc "Bill" `pamf`
    \x -> saw (x, y)        -- BILL saw MARY (IS)
s4 = foc "Bill" `pamf`
  \x -> foc "Bill" `pamf`
    \y -> saw (x, y)        -- BILL saw BILL (SS)
s5 = foc "Bill" `pamf`
  \y -> foc "Bill" `pamf`
    \x -> saw (x, y)        -- BILL saw BILL (IS)
s6 = foc "Bill" `pamf`
  \x -> foc "Sue" `pamf`
    \y -> saw (x, y)        -- BILL saw SUE (SS)
s7 = foc "Sue" `pamf`
  \y -> foc "Bill" `pamf`
    \x -> saw (x, y)        -- BILL saw SUE (SS)

(<~>) :: (Contrast f) => T -> f -> T
c <~> f = if contrast c f then point f else "that doesn't contrast"

-- some test cases
test :: [String]
test =
  [ ant <~> s0
  , ant <~> s1
  , ant <~> s2
  , ant <~> s3
  , ant <~> s4
  , ant <~> s5
  , ant <~> s6
  , ant <~> s7 ]

main :: IO ()
main = putStr . unlines $ test

showedTo :: (E, E, E) -> T
showedTo (x, y, z) = x ++ " showed " ++ y ++ " to " ++ z

ant1 :: T
ant1 = showedTo ("John", "Bill", "Mary")  -- John showed Bill to Mary

s8 = foc "Bill" `pamf`
  \x -> showedTo (x, "Bill", "Mary")      -- BILL showed Bill to Mary
s9 = foc "Bill" `pamf`
  \x -> foc "Mary" `pamf`
    \y -> foc "John" `pamf`
      \z -> showedTo (x, y, z)            -- BILL showed MARY to JOHN
s10 = foc "Bill" `pamf`
  \x -> foc "Mary" `pamf`
    \y -> foc "Mary" `pamf`
      \z -> showedTo (x, y, z)            -- BILL showed MARY to MARY (123)
s11 = foc "Bill" `pamf`
  \x -> foc "Mary" `pamf`
    \z -> foc "Mary" `pamf`
      \y -> showedTo (x, y, z)            -- BILL showed MARY to MARY (132)
s12 = foc "Mary" `pamf`
  \z -> foc "Bill" `pamf`
    \x -> foc "Mary" `pamf`
      \y -> showedTo (x, y, z)            -- BILL showed MARY to MARY (312)
s13 = foc "Mary" `pamf`
  \z -> foc "Mary" `pamf`
    \y -> foc "Bill" `pamf`
      \x -> showedTo (x, y, z)            -- BILL showed MARY to MARY (312)
s14 = foc "Mary" `pamf`
  \y -> foc "Bill" `pamf`
    \x -> foc "Mary" `pamf`
      \z -> showedTo (x, y, z)            -- BILL showed MARY to MARY (213)
s15 = foc "Mary" `pamf`
  \y -> foc "Mary" `pamf`
    \z -> foc "Bill" `pamf`
      \x -> showedTo (x, y, z)            -- BILL showed MARY to MARY (231)




{-- old
class Alts f where
  alts :: f -> [T]

instance Alts (F T) where
  alts (F x xs) = x : xs

instance {-# OVERLAPS #-} Alts a => Alts (F a) where
  alts (F x xs) = alts x ++ concatMap alts xs

class Point f where
  point :: f -> T

instance Point (F T) where
  point (F x xs) = x

instance {-# OVERLAPS #-} Point a => Point (F a) where
  point (F x xs) = point x

contrast :: (Point f, Alts f) => T -> f -> Bool
contrast c f = point f /= c && length [x | x <- alts f, x == c] == 1

-- could also just count occurrences of c directly
class Count f where
  count :: T -> f -> Int

instance Count (F T) where
  count c (F x xs) = helper c x + sum (map (helper c) xs)
    where helper c x = if c == x then 1 else 0

instance {-# OVERLAPS #-} Count a => Count (F a) where
  count c (F x xs) = count  c x + sum (map (count  c) xs)
--}

