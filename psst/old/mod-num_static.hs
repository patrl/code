module Main (main) where
import           Data.List

powerset :: [t] -> [[t]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ map (x:) (powerset xs)

powersetPlus :: Eq t => [t] -> [[t]]
powersetPlus xs = filter (/= []) $ powerset xs

type EBase = String
type E = [EBase]
type T = Bool

domainBase :: [EBase]
domainBase = ["B1","B2","B3","B4","M1","M2","M3","M4","M5","M6"]

domain :: [E]
domain = powersetPlus domainBase

boyBase :: [EBase]
boyBase = filter (\(x:xs) -> x == 'B') domainBase

movieBase :: [EBase]
movieBase = filter (\(x:xs) -> x == 'M') domainBase

seeBase :: [(EBase,EBase)]
seeBase = [("B1","M1"),
           ("B2","M2"), ("B2","M3"),
           ("B3","M3"), ("B3","M4"), ("B3","M5")]
--           ("B4","M6")]

boy :: [E]
boy = [xs | xs <- domain, all (`elem` boyBase) xs]

movie :: [E]
movie = [xs | xs <- domain, all (`elem` movieBase) xs]

see :: (E,E) -> T
see (xs,ys) = all (\x -> any (\y -> (x,y) `elem` seeBase) ys) xs &&
              all (\y -> any (\x -> (x,y) `elem` seeBase) xs) ys

sigma :: [E] -> E -> (E -> T) -> T
sigma np xs k = k xs && all (\ys -> not (k ys) || ys `intersect` xs == ys) np

exThreeBoys :: (((E -> T) -> T) -> T) -> T
exThreeBoys c = any (\xs -> c (sigma boy xs) && length xs == 3) domain

exFiveMovies :: (((E -> T) -> T) -> T) -> T
exFiveMovies c = any (\xs -> c (sigma movie xs) && length xs == 5) domain

test :: T
test = exThreeBoys (\m -> exFiveMovies (\n -> m (\x -> n (\y -> see (x,y)))))

witnesses :: [(E,E)]
witnesses = [(xs,ys) | xs <- domain, ys <- domain, sigma boy xs (\x -> sigma movie ys (\y -> see (x,y)))]

main :: IO ()
main = print witnesses
