data E = A | B | C | D | E | F | G | H | I | J
  deriving (Eq, Ord, Enum, Show)

type T = Bool

dom :: [E]
dom = [A ..]

setify :: (E -> T) -> [E]
setify p = do
  x <- dom
  if p x then return x else mempty

propify :: [E] -> E -> Bool
propify = flip elem

every :: (E -> T) -> (E -> T) -> T
every p q = all q $ setify p

some :: (E -> T) -> [E]
some = setify

the :: (E -> T) -> [E]
the p =
  if length xs == 1
    then xs
    else []
      where xs = setify p

liftQ quant p qs = do
  _ <- [True | every p (\x -> not . null $ qs x)]
  return $ quant p (\x -> any (== True) $ qs x)

main = print "hi"
