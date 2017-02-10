{-# LANGUAGE GADTs #-}

import Control.Monad

data Free f a = Pure a | Impure (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure x) = Pure $ f x
  fmap f (Impure m) = Impure $ fmap (fmap f) m

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure f <*> m = fmap f m
  Impure f <*> m = Impure $ fmap (<*> m) f

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= k = k a
  Impure m >>= k = Impure (fmap (>>= k) m)

eta :: Functor f => f a -> Free f a
eta = Impure . fmap Pure

data Lan g a where
  Lan :: g x -> (x -> a) -> Lan g a

instance Functor (Lan g) where
  fmap f (Lan gx h) = Lan gx (f . h)

lan :: g a -> Lan g a
lan ga = Lan ga id

data FFree g a where
  FPure   :: a -> FFree g a
  FImpure :: g x -> (x -> FFree g a) -> FFree g a

instance Functor (FFree g) where
  fmap f (FPure x)     = FPure (f x)
  fmap f (FImpure u q) = FImpure u (fmap f . q)

instance Applicative (FFree g) where
  pure = FPure
  FPure f     <*> x = fmap f x
  FImpure u q <*> x = FImpure u ((<*> x) . q)

instance Monad (FFree g) where
  return = FPure
  FPure x      >>= k = k x
  FImpure u k' >>= k = FImpure u (k' >>> k)
    where f >>> g = (>>= g) . f

--main = print "hi"
