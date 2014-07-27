import Data.List
import Text.PrettyPrint

import Prelude hiding ((^)) -- symbol used in Lambda_calc for abstraction
import Lambda_calc -- Oleg Kiselyov's lambda-term reducer:
                   -- http://okmij.org/ftp/Haskell/Lambda_calc.lhs
                   -- application: x#y == x(y); abstraction: x^M == \x.M;

[unit,bind] = map make_var ["unit", "bind"]

data Cat =   DP | S | N 
                | M Cat -- monadic Cat
                | F Cat Cat | B Cat Cat | FF Cat Cat | BB Cat Cat
--                /           \           //           \\
                  deriving (Eq, Show)

combine :: Cat -> Cat -> [(String, Term, Cat)]
combine l r = 
  lower $  
     [("Slash ", x^x, a) | F a b <- [l], b == r]
  ++ [("Backlash ", x^y^y#x, a) | B b a <- [r], b == l]
  ++ [("UnitRight " ++ rules, x^y^((bind#x)#(unit#y)), M c)
       | M a <- [l], (rules,z,c) <- combine a r]
  ++ [("UnitLeft " ++ rules, x^y^((bind#(unit#x))#y), M c)
       | M b <- [r], (rules,z,c) <- combine l b]
  ++ [("MonadLiftRight " ++ rules, x^y^k^x#(x^(bind#y)#(y^k#(z#x#y))), FF (M d) (BB c (M e)))
       | FF (M d) (BB a (M e)) <- [l], M b <- [r], (rules,z,c) <- combine a b]
  ++ [("MonadLiftLeft " ++ rules, x^y^k^((bind#x)#(x^y#(y^k#(z#x#y)))), FF (M d) (BB c (M e))) 
       | FF (M d) (BB b (M e)) <- [r], M a <- [l], (rules,z,c) <- combine a b]
  ++ [("MonadLiftUnitRight " ++ rules, x^y^k^x#(x^(bind#(unit#y))#(y^k#(z#x#y))), FF (M d) (BB c (M e)))
       | FF (M d) (BB a (M e)) <- [l], (rules,z,c) <- combine a r]
  ++ [("MonadLiftUnitLeft " ++ rules, x^y^k^((bind#(unit#x))#(x^y#(y^k#(z#x#y)))), FF (M d) (BB c (M e))) 
       | FF (M d) (BB b (M e)) <- [r], (rules,z,c) <- combine l b]
  ++ [("Combination " ++ rules, x^y^k^x#(x^y#(y^k#(z#x#y))), FF d (BB c f))
       | FF d (BB a e) <- [l], FF e' (BB b f) <- [r], e == e', (rules,z,c) <- combine a b]
  ++ [("LiftRight " ++ rules, x^y^k^x#(x^k#(z#x#y)), FF d (BB c e))
       | FF d (BB a e) <- [l], (rules,z,c) <- combine a r]
  ++ [("LiftLeft " ++ rules, x^y^k^y#(y^k#(z#x#y)), FF d (BB c e)) 
       | FF d (BB b e) <- [r], (rules,z,c) <- combine l b]

lower :: [(String, Term, Cat)] -> [(String, Term, Cat)]
lower exps = exps ++ [("Lower " ++ rules, x^y^z#x#y#(p^p), a)
                      | (rules, z, FF a (BB b c)) <- exps, b == c]
                  ++ [("MLower " ++ rules, x^y^z#x#y#unit, M a) 
                      | (rules, z, FF (M a') (BB a (M a''))) <- exps, a == a', a == a'']

-------------------------------------------------------------------------------


data Edge = Edge String Cat Term Int   Int String [Edge]  deriving (Eq, Show)
  --             phrase cat sem  start end recipe daughters

type Node = (String, Cat, Term) -- the string records the derivational recipe

findEdges :: [Edge] -> [Edge]
findEdges es =   [Edge (lstring ++ " " ++ rstring) cat (sem#lsem#rsem) lmin rmax rule [l, r] | 
                   l@(Edge lstring lcat lsem lmin lmax _ _) <- es,
                   r@(Edge rstring rcat rsem rmin rmax _ _) <- es,
                   lmax == rmin,
                   (rule, sem, cat) <- combine lcat rcat]
{-
              ++ [Edge lstring cat (sem#lsem) lmin lmax rule [l] |
                   l@(Edge lstring lcat lsem lmin lmax _ _) <- es, 
                   (rule, sem, cat) <- lower lcat]
-}

close :: Eq a => ([a] -> [a]) -> [a] -> [a] -- close a set under an op that finds new members
close op l = let new = union l (op l) in
               if (new == l) then l else close op new

prettyCat :: Cat -> Doc
prettyCat  (B a c)  = parens (prettyCat a <> text "\\"   <> prettyCat c)
prettyCat  (F a c)  = parens (prettyCat a <> text "/"    <> prettyCat c)
prettyCat  (BB a c)  = parens (prettyCat a <> text "\\\\" <> prettyCat c)
prettyCat  (FF a c)  = parens (prettyCat a <> text "//"   <> prettyCat c)
prettyCat  (M a)     = parens (text "M" <> prettyCat a)
prettyCat  a         = text (show a)

prettyEdge :: Edge -> Doc
prettyEdge (Edge phrase cat sem start end recipe daughters) = 
  let details = text phrase <> text " " <> 
                prettyCat cat <> text " " <> 
                text recipe <> text " " <> 
                text (show (eval sem)) in
    case daughters of 
      [] -> text "  " <> details
      [a] -> text "  " <> (details $+$ prettyEdge a)
      [a,b] -> text "  " <> (details $+$ prettyEdge a $+$ prettyEdge b)

--------------------------------------------------------------------------------------------

[k,d] = map make_var ["k","d"] -- convenient variables for semantic values

lexicon =  
  [("friend-of", ((F N DP),                                      (make_var "friend"))),
   ("mother",    ((B DP DP),                                     (make_var "mother"))),
   ("man",       (N,                                              (make_var "man"))),
   ("woman",     (N,                                              (make_var "woman"))),
   ("person",    (N,                                              (make_var "person"))),
   ("does",      ((F S S),                                       (x^x))),
   ("everyone",  ((FF S (BB DP S)),                               (make_var "forall"))),
   ("someone",   ((FF S (BB DP S)),                               (make_var "exists"))),
   ("nothing",   ((FF S (BB DP S)),                               (make_var "nothing"))),
   ("love",      ((F (B DP S) DP),                              (make_var "love"))),
   ("loves",     ((F (B DP S) DP),                              (make_var "loves"))),
   ("saw",       ((F (B DP S) DP),                              (make_var "saw"))),
   ("gave",      ((F (F (B DP S) DP) DP),                       (make_var "gave"))),
   ("thinks",    ((F (B DP S) S),                               (make_var "thinks"))),
   ("John",      (DP,                                             (make_var "j"))),
   ("Mary",      (DP,                                             (make_var "m"))),
   ("left",      ((B DP S),                                      (make_var "left"))),
   ("aman",     ((M DP),                                        (make_var "aman"))),
   ("evling",    ((FF (M S) (BB DP (M S))),                     (make_var "evling"))),
   ("evdog",    ((FF (M S) (BB DP (M S))),                     (make_var "evdog")))
  ]

go :: [String] -> Int -> [Edge]
go [] _ = []
go (word:tail) i = case lookup word lexicon of 
                     Just (cat, sem) -> (Edge word cat sem i (i+1) "" []) : (go tail (i+1))
                     Nothing -> error ("\'" ++ word ++ "\' not found in lexicon.\n")

s1 = ["aman", "left"]
s2 = ["John", "saw", "aman"]
s3 = ["evling", "left"]
s4 = ["aman", "saw", "evling"]
s5 = ["evling", "saw", "evdog"]

parse s = 
    map (\x -> (text "\n") <+> prettyEdge x) 
        (filter (\(Edge _ _ _ l r _ _) -> ((r - l) == length(s)))
                (close findEdges (go s 0))
        )
