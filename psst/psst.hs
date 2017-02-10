import           Control.Arrow ((>>>))
import           Data.List

type EBase = String -- atoms
type E = [EBase] -- atoms and non-atoms

data Var = W | X | Y | Z deriving (Show, Eq)
vars :: [Var]
vars = [W, X, Y, Z]

type S = Var -> E -- type of assignments
type C = [S] -- type of contexts
type U = C -> C -- type of updates on contexts

-- atomic predicates
--
domainBase :: [EBase] -- the atomic domain
domainBase = ["B1","B2","B3","B4","B5","B6",
              "G1","G2","G3","G4","G5","G6",
              "M1","M2","M3","M4","M5","M6"]

boyBase :: [EBase] -- the atomic boys
boyBase = filter (\s -> init s == "B") domainBase

girlBase :: [EBase] -- the atomic girls
girlBase = filter (\s -> init s == "G") domainBase

movieBase :: [EBase] -- the atomic movies
movieBase = filter (\s -> init s == "M") domainBase

sawBase :: [(EBase,EBase)] -- the atomic seeing relation
sawBase = [("B2","M2"), -- ("B2","M3"),
           ("B3","M2"), ("B3","M3"), ("B3","M4"),
           ("B4","M4"), ("B4","M5"), ("B4","M6")]
-- The above pairs should make 'ex3 boys saw ex5 movies' true...
           ++ [("B1","M1")]
-- ...But adding these pairs should falsify it. Brasoveanu's semantics doesn't
-- without post-suppositions (indeed, the non-post-suppositional semantics finds
-- two possible drefs for 'ex3 boys' in the second scenario: B1+B2+B4 and
-- B2+B3+B4). Using an update semantics lets us get the right result without
-- post-suppositions (surprisingly?). See especially the discussion of `distUpd`
-- and `exactlyD` below.

showedBase :: [(EBase,EBase,EBase)] -- the atomic showing relation
showedBase = [("B1", "G1", "M1"),
              ("B2", "G2", "M2")]

-- plural predicates
--
powerset :: [t] -> [[t]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ map (x:) (powerset xs) -- 2^(x:xs)!

powersetPlus :: Eq t => [t] -> [[t]]
powersetPlus xs = filter (/= []) $ powerset xs

domain :: [E] -- atomic and non-atomic individual
domain = powersetPlus domainBase

boys :: [E] -- atomic and non-atomic boys
boys = [xs | xs <- domain, all (`elem` boyBase) xs]

girls :: [E] -- atomic and non-atomic girls
girls = [xs | xs <- domain, all (`elem` girlBase) xs]

movies :: [E] -- atomic and non-atomic movies
movies = [xs | xs <- domain, all (`elem` movieBase) xs]

saw :: Var -> Var -> U -- 'see' is lexically cumulative
saw v u ss =
  [s | s <- ss,
       all (\x -> any (\y -> (x,y) `elem` sawBase) $ s v) $ s u,
       all (\y -> any (\x -> (x,y) `elem` sawBase) $ s u) $ s v]

showed :: Var -> Var -> Var -> U -- 'showed' is lexically cumulative
showed iobj dobj subj ss =
  [s | s <- ss,
       all (\x -> any (\y -> any (\z -> (x,y,z) `elem` showedBase) $ s dobj) $ s iobj) $ s subj,
       all (\y -> any (\x -> any (\z -> (x,y,z) `elem` showedBase) $ s dobj) $ s subj) $ s iobj,
       all (\z -> any (\x -> any (\y -> (x,y,z) `elem` showedBase) $ s iobj) $ s subj) $ s dobj]

-- DPs
--
type Tower a = (a -> U) -> U -- the type of scope-taking a's

put :: E -> Var -> S -> S -- assignment modification
put x i s j
  | i == j = x
  | otherwise = s j

some :: [E] -> Var -> U  -- nondeterministic re-assignment, restricted by np
some np i ss = [put x i s | s <- ss, x <- np]

noGreaterThan :: Var -> S -> S -> Bool -- selective supremum check
noGreaterThan i s1 s2 =
  length (s1 i `intersect` s2 i) < length (s1 i) ||
  (all (`elem` s2 i) (s1 i) && all (`elem` s1 i) (s2 i))

sigma :: Var -> U -- selective maximization
sigma i ss = [s | s <- ss, all (noGreaterThan i s) ss]

num :: Int -> Var -> U -- cardinality test
num n i ss = [s | s <- ss, length (s i) == n]

exactly :: Int -> [E] -> Var -> Tower Var -- lexical entry for 'exactly'
exactly n np i c = some np i >>> c i >>> sigma i >>> num n i
-- (f >>> g) x == g $ f x

-- For comparison, an entry that differs only in that the nuclear scope is
-- processed 'point-wise'/'distributively'. That's the key: whether the nuclear
-- scope ('saw exactly five movies') has access to all the boys at once, or
-- whether it just sees one plurality of boys at a time. In the latter case,
-- `distUpd (c i)` retains individuals pluralities of boys who saw exactly five
-- movies between them -- but that's not the cumulative reading we're after. In
-- the former case (typified by `exactly`), maximization over movies happens
-- with respect to the entire group of boys. Thus, the biggest plurality of
-- movies seen by any boys is selected.
--
distUpd :: U -> U
distUpd u ss = concat [u [s] | s <- ss]

exactlyD :: Int -> [E] -> Var -> Tower Var
exactlyD n np i c = some np i >>> distUpd (c i) >>> sigma i >>> num n i

-- One last check: `exactlyU` should work the same as `exactly` (and it does).
-- Notice that the logical form `exactlyU` gives you for 'ex3 boys saw ex5
-- movies' looks just like the problematic one that Brasoveanu argues motivates
-- post-suppositions: i.e., 'ex5 movies' ends up caught within the scope of the
-- maximization and dref introduction contributed by 'ex3 boys'. But the correct
-- meaning is derived in the update semantics without post-suppositions.
--
sigmaU :: Var -> U -> U
sigmaU i box ss = [s | s <- updated, all (noGreaterThan i s) updated]
  where updated = box ss

exactlyU :: Int -> [E] -> Var -> Tower Var -- lexical entry for 'exactly'
exactlyU n np i c = sigmaU i (some np i >>> c i) >>> num n i

-- printing
--
base :: C -- the initial context
base = [const []]

sho :: U -> [[(Var,E)]] -- displaying updates as lookup tables
sho u = [map (\v -> (v, f v)) vars | f <- u base]

main :: IO ()
main = do
  putStrLn "\nFirst, checking 'ex3 boys saw ex5 movies'..."
  putStrLn "\n** `exactly` returns the following assignments:"
  printish . sho $ exactly 3 boys X (\x -> exactly 5 movies Y (`saw` x))
  putStrLn "\n** now, with inverse scope"
  printish . sho $ exactly 5 movies Y (\y -> exactly 3 boys X (y `saw`))
  putStrLn "\n** `exactlyD` returns the following assignments:"
  printish . sho $ exactlyD 3 boys X (\x -> exactlyD 5 movies Y (`saw` x))
  putStrLn "\n** `exactlyU` returns the following assignments:"
  printish . sho $ exactlyU 3 boys X (\x -> exactlyU 5 movies Y (`saw` x))
  putStrLn "\nNow, checking 'ex1 boy showed ex1 girl ex1 movie'..."
  putStrLn "\n** `exactly` returns the following assignments:"
  printish . sho $ exactly 1 boys X (\x -> exactly 1 girls Y (\y -> exactly 1 movies Z (\z -> showed y z x)))
  putStrLn "\n** `exactlyD` returns the following assignments:"
  printish . sho $ exactlyD 1 boys X (\x -> exactlyD 1 girls Y (\y -> exactlyD 1 movies Z (\z -> showed y z x)))
  putStrLn "\n** `exactlyU` returns the following assignments:"
  printish . sho $ exactlyU 1 boys X (\x -> exactlyU 1 girls Y (\y -> exactlyU 1 movies Z (\z -> showed y z x)))
    where printish [] = putStrLn "😱"
          printish xs = mapM_ print xs








{--
 - some old notes
 -
  -- point-wise versions of the update-y functions
  --
  type UPW = S -> [S]
  type TowerPW a = (a -> UPW) -> UPW

  exactlyPW :: Int -> [E] -> Var -> TowerPW Var
  exactlyPW n np i k g = exactly n np i (\j ss -> concatMap (k j) ss) [g]

  seePW :: Var -> Var -> UPW
  seePW v u s = see v u [s]

  pwTest :: [[(Var,E)]]
  pwTest = sho (\ss -> concat [exactlyPW 3 boys X (\x -> exactlyPW 5 movies Y (`seePW` x)) s | s <- ss])

  -- Exploring how interleaving `some` and `sigma` gives the problematic reading:
  --
  goodTest =
    num 3 X . sigma X . num 5 Y . sigma Y . see Y X . some movies Y . some boys X

  badTest =
    num 3 X . sigma X . (some boys X <@> (num 5 Y . sigma Y . (some movies Y <@> see Y X)))
    where (u1 <@> u2) ss = [s' | s <- u1 ss, s' <- u2 [s]]

-- For comparison, a Brasoveanu-style sigma and 'exactly' which yields the
-- too-weak reading.
--
sigmaB :: [E] -> Var -> Tower Var
sigmaB np i k ss =
  [s' | s' <- drefs, all (noGreaterThan i s') drefs]
  where drefs = [s' | s <- some np i ss, s' <- k i [s]]

exactlyB :: Int -> [E] -> Var -> Tower Var
exactlyB n np i k = num n i . sigmaB np i k

-- On the other hand, the following looks very close to sigmaB but behaves
-- correctly in exactlyB. Leads me to suspect the key point is whether
-- maximizations and dref introductions end up interleaved. Notice, also, that
-- sigmaB is more 'point-wise' than sigmaX.
--
sigmaX :: [E] -> Var -> Tower Var
sigmaX np i k ss =
  [s' | s' <- drefs, all (noGreaterThan i s') drefs]
  where drefs = (some np i >>> k i) ss -- compare to drefs line in sigmaB

exactlyX :: Int -> [E] -> Var -> Tower Var
exactlyX n np i k = sigmaX np i k >>> num n i
 -
 -
--}
