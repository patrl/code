import Control.Monad

type E = Int

he :: E -> E
he = id

nioj :: a -> (a -> a -> b) -> b
nioj = flip join

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

s :: E
s = 5 `nioj` \x -> he <&> \y -> y `nioj` \z -> he <&> \v -> x + y + x + v

main = print s
