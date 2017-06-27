-- Erwig & Kollmansberger (2006,JFP)

import Control.Monad

newtype P a = P { unP :: [(a,Float)] } deriving (Show,Eq)

instance Monad P where
  return x  = P [(x,1)]
  P a >>= f = P [(y,m*n) | (x,m) <- a,(y,n) <- unP $ f x]

instance Applicative P where
  pure  = return
  (<*>) = ap

instance Functor P where
  fmap f m = pure f <*> m

certainly, impossible :: a -> P a
certainly    = return
impossible x = P [(x,0)]
