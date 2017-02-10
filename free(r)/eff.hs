data It i a = Pure a | Get (i -> It i a)

instance Functor (It i) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Get g)  = Get (fmap f . g)

instance Applicative (It i) where
  pure = Pure
  f <*> x = f >>= \f' -> x >>= \x' -> return $ f' x'

instance Monad (It i) where
  return = Pure
  Pure x >>= k = k x
  Get k' >>= k = Get (k' >>> k)

(>>>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >>> g = (>>= g) . f
