module FocusMonad where

data Focused e a =
    Normal a
  | FMarked e (Focused e (e -> a)) deriving Show

instance Show (a -> b) where
  show f = "<fun>"

run :: Focused e a -> a
run (Normal a) = a
run (FMarked e f) = run f e


instance Functor (Focused e) where
  fmap f (Normal a)    = Normal (f a)
  fmap f (FMarked e a) = FMarked e (fmap (f .) a)

instance Monad (Focused e) where
  return = Normal
  m >>= k = run $ fmap k m

instance Applicative (Focused e) where
  pure = return
  mf <*> mx = mf >>= \f -> mx >>= \x -> return (f x)


hmm :: Focused Int Int
hmm = FMarked 1 (FMarked 2 (Normal (+)))

hmk :: Int -> Focused Int Int
hmk = \x -> FMarked x (FMarked 7 (Normal (*)))

hmg :: Int -> Focused Int Int
hmg = \x -> FMarked 5 (FMarked x (Normal (-)))


main :: IO ()
main = do
  print $ "Right ID: " ++ show (run $ hmm >>= return) ++ " == " ++ show (run hmm)
  print $ "Left ID: " ++ show (run $ return 4 >>= hmk) ++ " == " ++ show (run $ hmk 4)
  print $ "Assoc: " ++ show (run $ hmm >>= hmk >>= hmg) ++ " == " ++ show (run $ hmm >>= \x -> hmk x >>= hmg)
