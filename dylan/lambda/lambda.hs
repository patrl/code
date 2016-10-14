{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes        #-}
import           Data.Foldable
import           Data.Traversable

data Exp a
  = Var a
  | App (Exp a) (Exp a)
  | Lam (Exp (Maybe a))
  deriving (Functor, Foldable, Traversable, Show)

instance Applicative Exp where
  pure = Var
  mf <*> mx
    = do f <- mf
         x <- mx
         return $ f x

instance Monad Exp where
  return = Var
  Var a >>= f = f a
  App l r >>= f = App (l >>= f) (r >>= f)
  Lam xs >>= f = undefined

main = print "Did you finish (>>=)?"

data T = C (forall a. a)
