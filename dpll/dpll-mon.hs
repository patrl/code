{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TupleSections #-}

-- monadz
--
import Control.Monad

newtype D a = D { unD :: G -> [(a,G)] }

instance Monad D where
  return x = D $ return . (x,)
  D m >>= f = D $ (>>= uncurry (unD . f)) . m

instance Applicative D where
  pure = return
  mf <*> mx = do {f <- mf; x <- mx; return $ f x}

instance Functor D where
  fmap f mx = pure f <*> mx

-- base types
--
type E = Int
type T = Bool

-- assignments etc
--
data Var = X | Y | Z deriving (Show, Eq)
type A = Var -> Maybe E
type G = [A]

gStart :: G
gStart = [const Nothing]

modify :: Var -> E -> A -> A
modify v x g = \v' -> if v == v' then Just x else g v'

beta :: Var -> (E -> D a) -> E -> D a
beta v f x = D (unD (f x) . map (modify v x))

push :: Var -> D E -> D E
push v m = do {x <- m; beta v return x}

-- lexical entries
--
univ :: [E]
univ = [1..6]

a :: (E -> D T) -> D E
a f = D $ \gs -> [(x,hs) | x <- univ, (True,hs) <- unD (f x) gs]

anOdd :: D E
anOdd = a (return . odd)

anEven :: D E
anEven = a (return . even)

every :: (E -> D T) -> (E -> D T) -> D T
every f g = D $ \gs ->
  [(
    all (\(D m, hs) -> any (\(p, is) -> p) (m hs)) (unD mm gs),
    concat [hs | (True, hs) <- unD (join mm) gs]
  )]
    where mm = fmap g $ a f

--pro :: Var -> D E
pro v = D $ \gs -> [([g v | g <- gs], gs)]

-- showing and displaying
--
instance Show A where
  show a = "|"++
           (init . init)
           (concat [show v ++"->"++ show (a v) ++", " | v <- [X,Y,Z]])
           ++"|"

instance Show a => Show (D a) where
  show (D m) = show (m gStart)

display :: Show a => D a -> IO ()
display (D m) = sequence_ $ map (putStrLn . show) (m gStart)

main :: IO ()
main = display m
  where m = every (return . odd) $ f
        f x = do x' <- push X (return x)
                 y  <- push Y anEven
                 return $ x' < y
