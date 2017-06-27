{-# LANGUAGE MultiParamTypeClasses #-}

import Control.Monad
import Data.Functor.Compose

newtype R r a = R { unR :: r -> a }

instance Monad (R r) where
  return = R . return
  R m >>= f = R (f . m >>= unR)

instance Applicative (R r) where
  pure = return
  mf <*> mx = do { f <- mf; x <- mx; return $ f x }

instance Functor (R r) where
  fmap f m = pure f <*> m

pro :: R a a
pro = R id

g :: (a -> b) -> R r a -> R r b
g = fmap

(<@>) :: R r a -> (a -> b) -> R r b
(<@>) = flip g  -- applied to pro, gives S&B meaning

--z :: (a -> r -> b) -> R r a -> r -> b
--z f m = unR m >>= f

--(<@@>) :: R r a -> (a -> r -> b) -> r -> b
--(<@@>) = flip z

beta :: (a -> R a b) -> a -> b
beta = (>>= unR)

uncurryR :: R r (R s a) -> R (r,s) a  -- assignments on demand
uncurryR (R m) = R $ uncurry (unR . m)

curryR :: R (r,s) a -> R r (R s a)
curryR (R m) = R $ R . curry m

type E = Int
type T = Bool

et,st :: (E -> T) -> T
et f = all f [1..10]
st f = any f [1..10]

test1 :: T
test1 = et $ beta (\x -> pro <@> \y -> x == y) -- everything == itself

newtype ST r a = ST { unST :: r -> (a,r) }

instance Monad (ST r) where
  return = ST . (,)
  ST m >>= f = ST $ uncurry (unST . f) . m

instance Applicative (ST r) where
  pure = return
  mf <*> mx = do { f <- mf; x <- mx; return $ f x }

instance Functor (ST r) where
  fmap f m = pure f <*> m

proD :: ST a a
proD = ST $ join (,)

{- some mix of uncurry,
 - pair functors -}

counit :: (a, a -> b) -> b
counit (x,f) = f x
-- m >>= f = fmap counit (fmap (fmap f) m)

counitN :: [(a, a -> [b])] -> [b]
counitN = concatMap counit
-- m >>= f = fmap counitN (fmap (fmap (fmap f)) m)

main = print "hello"
