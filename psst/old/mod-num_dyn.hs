module Main (main) where
import           Data.List

type EBase = String
type E = [EBase]

data Var = W | X | Y | Z deriving (Show, Eq)

vars :: [Var]
vars = [W, X, Y, Z]

type S = Var -> E
type C = [S]
type U = C -> C

-- atomic predicates
--
domainBase :: [EBase]
domainBase = ["B1","B2","B3","B4","B5","B6",
              "M1","M2","M3","M4","M5","M6"]

boyBase :: [EBase]
boyBase = filter (\s -> init s == "B") domainBase

movieBase :: [EBase]
movieBase = filter (\s -> init s == "M") domainBase

seeBase :: [(EBase,EBase)]
seeBase = [("B1","M1"),
           ("B2","M2"), ("B2","M3"), ("B2","M4"),
           ("B3","M3"), ("B3","M4"), ("B3","M5")]
--         this model makes 'ex3 boys saw ex5 movies' true
--         ++ [("B4","M6")] -- this model falsifies it

-- plural predicates
--
powerset :: [t] -> [[t]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ map (x:) (powerset xs) -- 2^(x:xs)!

powersetPlus :: Eq t => [t] -> [[t]]
powersetPlus xs = filter (/= []) $ powerset xs

domain :: [E]
domain = powersetPlus domainBase

boys :: [E]
boys = [xs | xs <- domain, all (`elem` boyBase) xs]

movies :: [E]
movies = [xs | xs <- domain, all (`elem` movieBase) xs]

see :: (S -> E) -> (S -> E) -> U -- 'see' is lexically cumulative
see v u ss = [s | s <- ss,
                    all (\x -> any (\y -> (x,y) `elem` seeBase) $ v s) $ u s,
                    all (\y -> any (\x -> (x,y) `elem` seeBase) $ u s) $ v s]

-- DPs
--
type Tower a = (a -> U) -> U
type TTower a = (Tower a -> U) -> U
type TTTower a = (TTower a -> U) -> U

put :: E -> Var -> S -> S -- assignment modification
put x i s j
  | i == j = x
  | otherwise = s j

some :: [E] -> Var -> Tower (S -> E) -- indefinite determiner
some np i k ss = [s' | s <- ss,
                       x <- np,
                       s' <- k (const x) [put x i s]]

sigma :: Var -> U -> U -- selective maximization
sigma i u ss = [s | s <- u ss,
                    all (\s' ->  s i `intersect` s' i == s' i) $ u ss]

num :: Int -> Var -> U -> U -- selective cardinality test
num n i u ss = [s | s <- u ss,
                    length (s i) == n]


exactly :: Int -> [E] -> Var -> TTower (S -> E) -- putting it all together
exactly n np i c = num n i $ c (sigma i . some np i)

-- adding distributivity: externally static
--
dist :: Tower (S -> E) -> Tower (S -> E)
dist m k = m (\xs ss -> [s | s <- ss,
                             all (\x -> not $ null (k (const [x]) [s])) $ xs s])

-- some helpful composition combinators
--
lift :: a -> Tower a
lift x k = k x

intLift :: Tower a -> TTower a
intLift m c = m $ c . lift

ll :: Tower a -> Tower (a -> b) -> Tower b
m `ll` n = \k -> m (\x -> n (\f -> k $ f x))

rr :: Tower (a -> b) -> Tower a -> Tower b
m `rr` n = \k -> m (\f -> n $ k . f)

lll :: TTower a -> TTower (a -> b) -> TTower b
m `lll` n = \c -> m (\m' -> n (\n' -> c $ m' `ll` n'))

rrr :: TTower (a -> b) -> TTower a -> TTower b
m `rrr` n = \c -> m (\m' -> n (\n' -> c $ m' `rr` n'))

llll :: TTTower a -> TTTower (a -> b) -> TTTower b
m `llll` n = \c -> m (\m' -> n (\n' -> c $ m' `lll` n'))

rrrr :: TTTower (a -> b) -> TTTower a -> TTTower b
m `rrrr` n = \c -> m (\m' -> n (\n' -> c $ m' `rrr` n'))

lower :: Tower U -> U
lower m = m id

llower :: TTower U -> U
llower m = m lower

lllower :: TTTower U -> U
lllower m = m llower

-- a test case: ex3 boys saw ex5 movies
-- nota bene: accidental co-indexation predicts falsity! sad!
--
test :: U
test = llower $
       lll
         (exactly 3 boys X)
         (rrr
           (lift $ lift see)
           (exactly 5 movies Y)
         )

-- another: ex2 boys dist saw ex3 movies (true: B2 and B3 each did)
--
distE2B :: TTTower (S -> E) -- dist + ex1 boy: dist first applies,
                            -- then intLift lifts the distribution
                            -- over any downstream cardinality tests
distE2B = rr
            (lift intLift)
            (rr
              (lift dist)
              (exactly 2 boys X)
            )

testDist :: U
testDist = lllower $
           llll
             distE2B
             (rrrr
               (lift . lift . lift $ see)
               (lift $ exactly 3 movies Y)
             )

-- printing
--
base :: C -- the initial context
base = [const []]

sho :: U -> [(Var,E)] -- displaying updates as (unions of) lookup tables
sho u = [(v, e) | v <- vars,
                  f <- u base,
                  e <- [f v]]

main :: IO ()
main = do {print $ sho test;
           print $ sho testDist}
