import           Data.Function
import           Data.List

data Type = DP | S | NP | FS Type Type
          | BS Type Type | FF Type Type | BB Type Type
  deriving (Show, Eq)
data Tree = Atom String
          | FA TTree TTree
          | BA TTree TTree
          | LL TTree TTree
          | LR TTree TTree
          | Comb TTree TTree
          | Lower TTree TTree
  deriving (Show, Eq)

type TTree = (Tree, [Type])
type Sentence = [TTree]

sentence :: String -> Sentence
sentence = map wordToTTree . words
  where wordToTTree w = (Atom w, wordTypes w)

-- lexicon
--
wordTypes :: String -> [Type]
wordTypes w
  | w == "everyone" = [FF S (BB DP S)]
  | w == "someone" = [FF S (BB DP S)]
  | w == "dylan" = [DP]
  | w == "simon" = [DP]
  | w == "boy" = [NP]
  | w == "binoculars" = [NP]
  | w == "elk" = [NP]
  | w == "the" = [FS DP NP]
  | w == "left" = [BS DP S]
  | w == "saw" = [FS (BS DP S) DP]
  | w == "gave" = [FS (FS (BS DP S) DP) DP]
  | w == "showed" = [FS (FS (BS DP S) DP) DP]
  | w == "with" = [FS (BS (BS DP S) (BS DP S)) DP, FS (BS NP NP) DP]

-- parsing
--
splits :: [a] -> [([a], [a])]
splits ts = [f ts | f <- map splitAt [1..length ts - 1]]

ttrees :: Sentence -> [TTree]
ttrees [] = []
ttrees [t] = [t]
ttrees ts = [t | (ls,rs) <- splits ts, l <- ttrees ls,
                                       r <- ttrees rs,
                                       t <- combine l r]

combine :: TTree -> TTree -> [TTree]
combine l r = app (FA l r) ++ app (BA l r) ++ app (LR l r) ++ app (LL l r)

app :: Tree -> [(Tree, [Type])]
app (FA (a, ts) (b, ss))
  = [(FA (a, [FS x y]) (b, [y]), [x]) | FS x y <- ts, z <- ss, y == z]
app (BA (a, ts) (b, ss))
  = [(BA (a, [x]) (b, [BS x y]), [y]) | BS x y <- ss, z <- ts, x == z]
app (LR (a, ts) (b, ss))
  = [(LR (a, [FF x (BB y z)]) (b, [BS u v]), [FF x (BB v z)]) | FF x (BB y z) <- ts, BS u v <- ss, u == y]
    ++
    [(LR (a, [FF x (BB (FS v u) z)]) (b, [y]), [FF x (BB v z)]) | FF x (BB (FS v u) z) <- ts, y <- ss, u == y]
app (LL (a, ts) (b, ss))
  = [(LL (a, [FS v u]) (b, [FF x (BB y z)]), [FF x (BB v z)]) | FS v u <- ts, FF x (BB y z) <- ss, u == y]
    ++
    [(LL (a, [y]) (b, [FF x (BB (BS u v) z)]), [FF x (BB v z)]) | y <- ts, FF x (BB (BS u v) z) <- ss, u == y]

parse :: String -> [TTree]
parse = ttrees . sentence

prettyCat :: Type -> String
prettyCat cat = case cat of
  FS x y -> "(" ++ prettyCat x ++ " / " ++ prettyCat y ++ ")"
  BS x y -> "(" ++ prettyCat x ++ " \\backslash " ++ prettyCat y ++ ")"
  FF x y -> "(" ++ prettyCat x ++ " \\sslash " ++ prettyCat y ++ ")"
  BB x y -> "(" ++ prettyCat x ++ " \\bbslash " ++ prettyCat y ++ ")"
  _ -> "\\text{" ++ show cat ++ "}"

pretty :: TTree -> [String]
pretty tree = case tree of
  (Atom x, ts) -> ["[{$" ++ prettyCat t ++ "$} [" ++ x ++ "] ]" | t <- ts]
  (FA x y, ts) ->
    ["[{$" ++ prettyCat t ++ "$} " ++ a ++ " " ++ b ++ " ]" |
      t <- ts, a <- pretty x, b <- pretty y]
  (BA x y, ts) ->
    ["[{$" ++ prettyCat t ++ "$} " ++ a ++ " " ++ b ++ " ]" |
      t <- ts, a <- pretty x, b <- pretty y]
  (LL x y, ts) ->
    ["[{$" ++ prettyCat t ++ "$} " ++ a ++ " " ++ b ++ " ]" |
      t <- ts, a <- pretty x, b <- pretty y]
  (LR x y, ts) ->
    ["[{$" ++ prettyCat t ++ "$} " ++ a ++ " " ++ b ++ " ]" |
      t <- ts, a <- pretty x, b <- pretty y]

wrapUp :: String -> String
wrapUp x = unlines $
  concatMap
  (map (\x -> "\\begin{forest}\n" ++ x ++ "\n\\end{forest}\n") . pretty) $
  parse x

main :: IO ()
main = putStr $
  wrapUp "the elk with the binoculars gave dylan the binoculars with the elk"

{--
fastTtrees = head . head . cache

cache :: Sentence -> [[[TTree]]]
cache [x] = [[[x]]]
cache (x:xs) = build x (transpose rs) : rs
  where rs = cache xs

build :: TTree -> [[[TTree]]] -> [[TTree]]
build a [] = [[a]]
build a (ts:tss) = g (reverse is) ts : is
  where is = build a tss
        g is ts = [r | (i,t) <- zip is ts,
                       ti <-i,
                       tt <-t,
                       r <- combine ti tt]

memoizedFib :: Int -> Integer
memoizedFib = (map fib [0 ..] !!)
 where fib 0 = 0
       fib 1 = 1
       fib n = memoizedFib (n-2) + memoizedFib (n-1)
--}
