{-# LANGUAGE FlexibleInstances, FunctionalDependencies #-}

class Apply f g ret | f g -> ret where
  app :: f -> g -> ret
instance Apply (a -> b) a b where
  f `app` x = f x
instance Apply a (a -> b) b where
  x `app` f = f x
