{-- to add: monads, semantics, binding[?] --}
import           Data.List

data Type = DP | S | NP | V | Stop        -- atomic cats
          | FS Type Type | BS Type Type   -- {/, \}
          | US Type Type                  -- | (for events/modification)
          | FF Type Type | BB Type Type   -- {//, \\}
  deriving (Show, Eq)

data Tree = Atom String | Bin String TTree TTree
  deriving (Show, Eq)

type TTree = (Tree, [Type])
type Sentence = [TTree]

sentence :: String -> Sentence
sentence = map lookup . words
  where lookup w = (Atom w, lexicon w)

-- lexicon
--
lexicon :: String -> [Type]
lexicon w
  | w == "everyone" = [FF S (BB DP S)]
  | w == "someone" = [FF S (BB DP S)]
  | w == "dylan" = [DP]
  | w == "simon" = [DP]
  | w == "agent" = [FS (US V S) DP]
  | w == "theme" = [FS (US V S) DP]
  | w == "goal" = [FS (US V S) DP]
  | w == "boy" = [NP]
  | w == "binoculars" = [NP]
  | w == "elk" = [NP]
  | w == "the" = [FS DP NP]
  | w == "every" = [FF (FF S (BB DP S)) (BB (FS S NP) S)]
  | w == "a" = [FF (FF S (BB DP S)) (BB (FS S NP) S)]
  | w == "no" = [FF (FF S (BB DP S)) (BB (FS S NP) S)]
  | w == "left" = [BS DP S, US V S]
  | w == "saw" = [FS (BS DP S) DP, US V S]
  | w == "gave" = [FS (FS (BS DP S) DP) DP, US V S]
  | w == "showed" = [FS (FS (BS DP S) DP) DP, US V S]
  | w == "thought" = [FS (BS DP S) S]
  | w == "and" = [FS (BS S S) S]
  | w == "with" = [FS (BS (BS DP S) (BS DP S)) DP, FS (BS NP NP) DP]
  | w == "gap" = [FF (BB DP S) (BB DP S)]                 -- infer gaps?
  | w == "acdgap" = [FF (FF (FF S (BB (BS DP S) S)) (BB DP (BS DP S))) (BB (FS (BS DP S) DP) (FF S (BB DP S)))]
    -- incompatible with rel clause islands!
    -- doesn't allow for any scopal things inside the ACD
  | w == "who" = [FS (BS NP NP) (BB DP S)]
  | w == "stop" = [Stop]                                  -- islands
  | w == "eclos" = [FS S (US V S)]

-- parsing
--
combine :: TTree -> TTree -> [TTree]
combine (a,ts) (b,ss) =
  [(Bin -- forward application
    "FA" (a, [FS x y]) (b, [y]), [x]) |
      FS x y <- ts, z <- ss, y == z]
  ++
  [(Bin -- backward application
    "BA" (a, [x]) (b, [BS x y]), [y]) |
      BS x y <- ss, z <- ts, x == z]
  ++
  [(Bin -- modification
    "Mod" (a, [x]) (b, [y]), [x]) |
      x <- ts, y <- ss, x == y, conjoinable x]
  ++
  [(Bin -- scoping L, then combining its 'trace' and R
    ("LR("++w++")") (a, [FF x (BB y z)]) (b, [u]), [FF x (BB v z)]) |
      FF x (BB y z) <- ts, u <- ss,
      (Bin w t1 t2, rs) <- combine (a, [y]) (b, [u]), v <- rs]
  ++
  [(Bin -- scoping R, then combining its 'trace' and L
    ("LL("++w++")") (a, [u]) (b, [FF x (BB y z)]), [FF x (BB v z)]) |
      u <- ts,
      FF x (BB y z) <- ss,
      (Bin w t1 t2, rs) <- combine (a, [u]) (b, [y]), v <- rs]
-- this is a 'functionally complete' set of combinators. dually continuized
-- combination (B&S's Combine) isn't required, though it's needed if you're
-- interested in the S&B/B&S account of crossover.

ttrees :: Sentence -> [TTree]
ttrees [] = []
ttrees [t] = [t]
ttrees ts =
  [t | (ls,rs) <- splits ts,
       l <- ttrees ls,
       r <- ttrees rs,
       t <- addLowers $ combine l r]  -- break in half multiple ways,
                                      -- try to combine the pieces
  ++
  [(Bin -- enforcing islands; must be at this 'higher' level, not in combine
        -- nota bene: this is still a bit hacky
    ("Island("++w++")") t1 t2, [s]) |
      (a, xs) <- [head ts], t <- xs, t == Stop,
      (Bin w t1 t2, ss) <- ttrees $ tail ts, s <- ss, evaluated s]

parse :: String -> [TTree]
parse = ttrees . sentence

-- helper functions for parsing
--
splits :: [a] -> [([a], [a])] -- return all possible cleavings of a list
splits ts = [f ts | f <- map splitAt [1..length ts - 1]]

addLowers :: [TTree] -> [TTree]
addLowers ttrees =
  ttrees
  ++
  [(Bin -- incorporating all possible lowerings of the ttrees in question
    ("Lower("++w++")") t1 t2, [tl]) |
      (Bin w t1 t2, ts) <- ttrees, t <- ts, tl <- tail $ closeUnderLower [t]]

closeUnderLower :: [Type] -> [Type]
closeUnderLower ts = let new = union ts (map collapse ts) in
  if new == ts then ts else closeUnderLower new

collapse :: Type -> Type
collapse t = case t of
  FF a (BB b c) -> if b == c then a else FF a (BB (collapse b) c)
  _ -> t

evaluated :: Type -> Bool
evaluated t = case t of
  FF a b -> False
  FS a b -> evaluated a
  US a b -> evaluated b
  BS a b -> evaluated b
  BB a b -> evaluated b
  _ -> True

conjoinable :: Type -> Bool
conjoinable t = case t of
  S -> True
  NP -> True
  FF a b -> conjoinable a
  FS a b -> conjoinable a
  US a b -> conjoinable b
  BS a b -> conjoinable b
  BB a b -> conjoinable b
  _ -> False

-- parsing concluded
-- here's the pretty printer
-- writes a tex file with trees of the sentence-type parses in your working dir
--
prettyCat :: Type -> String -- printing cats
prettyCat cat = case cat of
  FS x y -> "(" ++ prettyCat x ++ " / " ++ prettyCat y ++ ")"
  BS x y -> "(" ++ prettyCat x ++ " \\backslash " ++ prettyCat y ++ ")"
  US x y -> "(" ++ prettyCat x ++ "|" ++ prettyCat y ++ ")"
  FF x y -> "(" ++ prettyCat x ++ " \\sslash " ++ prettyCat y ++ ")"
  BB x y -> "(" ++ prettyCat x ++ " \\bbslash " ++ prettyCat y ++ ")"
  _ -> "\\text{" ++ show cat ++ "}"

pprettyCat :: Type -> String -- dropping outer parens
pprettyCat thing = case xs of
  [] -> []
  _ -> if head xs == '(' && last xs == ')'
       then drop 1 $ init xs
       else xs
  where xs = prettyCat thing

pretty :: TTree -> [String]
pretty tree = case tree of
  (Atom x, ts) -> ["[{$"++pprettyCat t++"$} ["++x++"] ]" | t <- ts]
  (Bin w x y, ts) ->
    ["[{$\\textbf{\\textsf{"++w++"}} \\vdash " ++
     pprettyCat t++"$} "++a++" "++b++" ]"
      |
     t <- ts, a <- pretty x, b <- pretty y]

toForest :: String -> String
toForest x = unlines $
  concatMap
  (map
    (\x -> "\\begin{forest}for tree={scale=.7}\n"++x++"\n\\end{forest}\n\\\\\n")
    . pretty) $
  filter (\t -> snd t == [S]) $
  parse x

toParse :: String
toParse = "the boy who stop gap saw everyone saw the elk who stop someone saw gap"

main :: IO ()
main = do
  putStr output
  writeFile "sandbox.tex" $ preamble++output++end
    where output = toForest toParse
          preamble =
            "\\documentclass{article}\n\\synctex=1\n" ++
            "\\usepackage[margin=.8in,landscape]{geometry}\n" ++
            "\\usepackage{forest,mathtools,newtxtext,newtxmath}\n" ++
            "\\newcommand\\bs\\backslash{}\n" ++
            "\\newcommand\\sslash{\\mathord{/\\mkern-5mu/}}\n" ++
            "\\newcommand\\bbslash{\\mathord{\\bs\\mkern-5.23mu\\bs}}\n" ++
            "\\begin{document}\n\n"
          end = "\\end{document}"
