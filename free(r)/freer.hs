{-# LANGUAGE GADTs, DeriveFunctor, UndecidableInstances #-}

import Control.Monad

data Free f a = Pure a | Impure (f (Free f a))

instance (Show a, Show (f (Free f a))) => Show (Free f a) where
  show (Pure x) = show x
  show (Impure m) = show m

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

newtype F a b = F { unF :: (a, (a -> b)) } deriving Functor

instance Show (a -> b) where
  show f = "<fun>"

instance Show a => Show (F a b) where
  show (F (a, f)) = show (a, f)

compose :: F a b -> b
compose (F (x, f)) = f x

foc :: a -> F a a
foc x = F (x, id)

test = do x <- eta $ foc 3
          y <- eta $ foc 2
          return $ x + y

test1 = do x <- eta [0,1]
           y <- eta [2,3]
           return $ x + y

test2 = do x <- eta $ Rooth (0, [0,1])
           y <- eta $ Rooth (5, [5,6])
           return $ x + y

data Rooth a = Rooth { unRooth :: (a, [a]) } deriving Functor

instance Show a => Show (Rooth a) where
  show (Rooth (x, xs)) = show (x, xs)

eval :: Free (F a) b -> b
eval (Pure x) = x
eval (Impure (F (x,f))) = eval $ f x
