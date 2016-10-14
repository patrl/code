import           Control.Arrow ((>>>))
import           Data.List

type EBase = String -- atoms
type E = [EBase] -- atoms and non-atoms

data Var = W | X | Y | Z deriving (Show, Eq)
vars :: [Var]
vars = [W, X, Y, Z]

type S = Var -> E -- type of assignments
type U = S -> [S] -- type of propositions (relations on assignments)

-- atomic predicates
--
domainBase :: [EBase] -- the atomic domain
domainBase = ["B1","B2","B3","B4","B5","B6",
              "M1","M2","M3","M4","M5","M6"]

boyBase :: [EBase] -- the atomic boys
boyBase = filter (\s -> init s == "B") domainBase

movieBase :: [EBase] -- the atomic movies
movieBase = filter (\s -> init s == "M") domainBase

seeBase :: [(EBase,EBase)] -- the atomic seeing relation
seeBase = [("B2","M2"), --("B2","M3"),
           ("B3","M2"), ("B3","M3"), ("B3","M4"),
           ("B4","M4"), ("B4","M5"), ("B4","M6")]
--         this model should make 'ex3 boys saw ex5 movies' true
           ++ [("B1","M1")]
--         this model should falsify it

-- plural predicates
--
powerset :: [t] -> [[t]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ map (x:) (powerset xs) -- 2^(x:xs)!

powersetPlus :: Eq t => [t] -> [[t]]
powersetPlus xs = filter (/= []) $ powerset xs

domain :: [E] -- atomic and non-atomic individuals
domain = powersetPlus domainBase

boys :: [E] -- atomic and non-atomic boys
boys = [xs | xs <- domain, all (`elem` boyBase) xs]

movies :: [E] -- atomic and non-atomic movies
movies = [xs | xs <- domain, all (`elem` movieBase) xs]

see :: Var -> Var -> U -- 'see' is lexically cumulative
see v u s = [s' | s' <- [s],
                  all (\x -> any (\y -> (x,y) `elem` seeBase) $ s v) $ s u,
                  all (\y -> any (\x -> (x,y) `elem` seeBase) $ s u) $ s v]

-- DPs
--
type Tower a = (a -> U) -> U -- the type of scope-taking a's

put :: E -> Var -> S -> S -- assignment modification
put x i s j
  | i == j = x
  | otherwise = s j

some :: [E] -> Var -> U -- random assignment
some np i s = [s' | x <- np, s' <- [put x i s]]

noGreaterThan :: Var -> S -> S -> Bool -- selective supremum check
noGreaterThan i s1 s2 =
  length (s1 i `intersect` s2 i) < length (s1 i) ||
  (all (`elem` s2 i) (s1 i) && all (`elem` s1 i) (s2 i))

sigma :: Var -> [S] -> [S] -- selective maximization
sigma i ss = [s | s <- ss, all (noGreaterThan i s) ss]

num :: Int -> Var -> [S] -> [S] -- selective cardinality test
num n i ss = [s | s <- ss, length (s i) == n]

(<^>) :: U -> U -> U -- dynamic conjunction (relation composition)
p <^> q = \s -> [s'' | s' <- p s, s'' <- q s']

exactly :: Int -> [E] -> Var -> Tower Var -- lexical entry for 'exactly'
exactly n np i c = some np i <^> c i >>> sigma i >>> num n i
-- compare `some np i >>> c i >>> sigma i >>> num n i` in the update-style
-- semantics, which (unlike this entry) gets correct results o_o

-- printing
--
base :: S -- the initial context
base = const []

sho :: U -> [[(Var,E)]] -- displaying updates as lookup tables
sho u = [map (\v -> (v, f v)) vars | f <- u base]

main :: IO ()
main = do
  putStrLn "\n`exactly` returns the following assignments:"
  printish . sho $ exactly 3 boys X (\x -> exactly 5 movies Y (`see` x))
    where printish [] = putStrLn "fail :("
          printish xs = mapM_ print xs
