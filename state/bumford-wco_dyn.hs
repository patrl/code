-- Haskell port of wco_dyn.ml using StateT transformer
-- with Lists to model nondeterminism within state

import Control.Monad.State

type Stack = [Int]
type DState a = StateT Stack [] a
type E = DState Int
  -- Stack -> [(Int, Stack)]
type T = DState Bool
  -- Stack -> [(Bool, Stack)]
type GQ = (E -> T) -> T


{- Auxiliary functions (not used)

class Booly a where
  truthy :: a -> Bool

instance Booly [(Bool, a)] where
  truthy xs = (or . map fst) xs

instance Booly Bool where
  truthy = id

if' :: (Booly b) => b -> a -> a -> a
if' boolyVal trueResult falseResult = 
  if truthy boolyVal then trueResult else falseResult

clean_up :: [(Bool,Stack)] -> [(Bool,Stack)]
clean_up xs = filter fst xs

pop :: Int -> Stack -> Stack
pop x []   = [x]
pop x (i:is) | x == i     = is++[x]
             | otherwise  = i:(pop x is)

-}


-- Auxiliary functions (potentially used)

firstToLast :: Stack -> Stack
firstToLast []     = []
firstToLast (x:xs) = xs++[x]

eval :: T -> [(Bool,Stack)]
eval m = runStateT m []

-- lift is a predefined function in MonadTrans class that 
-- converts the value(s) inside a monad (in this case a list)
-- to default transformers (in this case nondeterministic 
-- stateful computations: Stack -> [(a, Stack)])
--
-- lift' is just like lift, except that it returns unit'-like 
-- computations, in which x has been added to the resulting
-- state
lift' :: [Int] -> DState Int
lift' c = StateT $ \s -> c >>= (\x -> return (x,x:s))



-- The model and teh language


-- domain

univ = [1..10]


-- predicates

thing :: E -> T
thing m = do
  x <- m
  return (x `elem` univ)

equals, gthan :: E -> E -> T
equals r l = do
  x <- l
  y <- r
  return (x == y)

gthan r l = do
  x <- l
  y <- r
  return (x > y)


-- names update the stack, pronouns don't

john, bill, johnORbill:: E
john = do
  lift' [1]

bill = do
  lift' [2]
  
johnORbill = do
  lift' [1,2]


he, he1, he2 :: E
he = do
  xs <- get
  return (xs!!0)

he1 = do
  xs <- get
  return (xs!!1)

he2 = do
  xs <- get
  return (xs!!2)


-- connectives

conj :: T -> T -> T
conj p q = do
  b <- p
  b' <- q 
  return (b && b')

neg :: T -> T
neg p = do
  s <- get
  b <- p
  put s
  return (not b)

impl :: T -> T -> T
impl p q = neg (p `conj` (neg q))


-- determiners

some, every, test :: (E -> T) -> (E -> T) -> T
some p q = do
  s <- get
  x <- lift univ
  -- modify firstToLast
  b <- p (return x)
  b' <- q (lift' [x])
  if not (b && b') then lift [] else return True 

test p q = do
  x <- lift univ
  -- modify firstToLast
  b <- p (return x)
  b' <- q (lift' [x])
  return (not b || b')

every p q = do
  s <- get
  let xs = (runStateT $ test p q) s
  if not (all fst xs) then lift [] else put s; return True


-- generalized quantifiers

eo, so, he' :: (E -> T) -> T
eo = every thing

so = some thing

he' p = p he


-- scope

equals_lift :: GQ -> E -> T
equals_lift g l = do
  l' <- l
  g (\r -> equals r (return l'))

equals_ss, equals_ws :: GQ -> GQ -> T
equals_ss o s =
  s (\l -> do l' <- l
              o (\r -> do r' <- r
                          return (l'==r')))

equals_ws o s = 
  o (\r -> s (\l -> equals_ss ($ r) ($ l)))

