{-
Approximation of a Shan/Barker continuation-based grammar, e.g., Barker and Shan 2008.

* Lift and combine can be factored into three meta-rules that govern
  binary combination.  For any rule of the form A * B = C, there will
  be rules of the following forms:

     D|E   E|F  D|F    D|E        D|E        D|E   D|E
      A  *  B  = C  ,   A  * B  =  C  ,  A *  B  =  C

     Comb(ination),    LiftR(ight),      LiftL(eft)

  These rules correspond to normal left-to-right combination, Lift on
  the right-hand element, and Lift on the left-hand element,
  respectively.  Reapeated application of these metarules to the two
  basic combination rules (namely, Slash: A * A/B = B, and Backslash:
  B * B\A = A) will produce (almost, see below) all needed combination
  rules.  Given a pair of constituents, there will be a (relatively)
  small finite number of binary combination rules that can match those
  constituents.  Thus we don't start constructing combination rules
  till we have in view two particular constituents that need
  combining.

* This strategy does not find a way to combine

            S | S
        A / -----    with    B
              B

  let alone (if desired)

                 S | S              S | S
        A / (C \ -----)    with    (----- \ B)
                   B                  C

-}

--import Debug.Trace
import           Data.List
import           Lambda_calc
import           Prelude          hiding ((^))
                   -- http://okmij.org/ftp/Haskell/Lambda_calc.lhs
import           Data.List.Split
import           Text.PrettyPrint

data Cat = DP | N | S | F | BS Cat Cat | FS Cat Cat | BB Cat Cat | FF Cat Cat
  --                        \            /            \\           //
              | TN Cat Cat | Q Cat Cat | RD Cat Cat   deriving (Eq, Show)
  --            *            ?           >

data Edge = Edge String Cat Term Int   Int String [Edge]  deriving (Eq, Show)
  --             phrase cat sem  start end recipe daughters

type Node = (String, Cat, Term) -- the string records the derivational recipe

findEdges :: [Edge] -> [Edge]
findEdges es =   [Edge (lstring ++ " " ++ rstring) cat (sem#lsem#rsem) lmin rmax rule [l, r] |
                   l@(Edge lstring lcat lsem lmin lmax _ _) <- es,
                   r@(Edge rstring rcat rsem rmin rmax _ _) <- es,
                   lmax == rmin,
                   (rule, cat, sem) <- combine ("", lcat, lsem) ("", rcat, rsem)]
              ++ [Edge lstring cat (sem#lsem) lmin lmax rule [l] |
                   l@(Edge lstring lcat lsem lmin lmax _ _) <- es,
                   (rule, cat, sem) <- shift ("", lcat, lsem)]

close :: Eq a => ([a] -> [a]) -> [a] -> [a] -- close a set under an op that finds new members
close op l = let new = union l (op l) in
               if new == l then l else close op new

combine :: Node -> Node -> [Node] -- returns a list of all ways of combining two constituents
combine l@(lr,lc,ls) r@(rr,rc,rs) =
     case lc of (FS la lb) -> [("Slash",la,x^x) | lb == rc]
                (FF lc (BB la lb)) ->
                   map (\(nr,nc,ns) -> ("LiftR "++nr,
                                        FF lc (BB nc lb),
                                        (a^b^k^(a#(c^(k#(ns#c#b)))))))
                       (combine ("",la,x^x) r)
                otherwise -> []
  ++ case rc of (BS rb ra) -> [("Backslash",ra,x^y^y#x) | rb == lc]
                (FF rc (BB ra rb)) ->
                   map (\(nr,nc,ns) -> ("LiftL "++nr,
                                        FF rc (BB nc rb),
                                        (a^b^k^(b#(c^(k#(ns#a#c)))))))
                       (combine l ("",ra,x^x))
                otherwise -> []
  ++ case (lc,rc) of (FF lx (BB ly lz), FF rx (BB ry rz)) ->
                       if (lz == rx) then
                         map (\(nr,nc,ns) -> ("Comb "++nr,
                                              (FF lx (BB nc rz)),
                                              (a^b^k^(a#(c^(b#(d^(k#(ns#c#d)))))))))
                             (combine ("",ly,x^x) ("",ry,x^x))
                       else []
                     otherwise -> []
  ++ case lc of (FS la (FF c (BB b d))) ->
                   map (\(nr,nc,ns) -> ("LiftArg "++nr,la,x^y^(ns#x#(k^(k#y)))))
                       (combine ("", FS la b,x^x) r)
                otherwise -> []

shift :: Node -> [Node] -- returns a list of shifted constituents
shift (r,c,s) = case c of (FF (TN F a) b) -> [("Front", FS a b, x^x)]
                          (FF a (BB S S)) -> [("Lower", a, x^(x#(x^x)))]
                          (FF c (BB a b)) ->
                            map (\(nr,nc,ns) -> ("Embed "++nr,
                                                 FF c (BB nc b),
                                                 x^k^(x#(y^(k#(ns#y))))))
                                (shift ("",a,x^x))
                          otherwise -> []

--------------------------------------------------------------------------------------

prettyCat :: Cat -> Doc
prettyCat  (FF (RD DP S) (BB DP S)) = text "pn"  -- abbreviation
prettyCat  (BS a c)  = parens (prettyCat a <> text "\\"   <> prettyCat c)
prettyCat  (FS a c)  = parens (prettyCat a <> text "/"    <> prettyCat c)
prettyCat  (BB a c)  = parens (prettyCat a <> text "\\\\" <> prettyCat c)
prettyCat  (FF a c)  = parens (prettyCat a <> text "//"   <> prettyCat c)
prettyCat  (TN a c)  = parens (prettyCat a <> text "*"    <> prettyCat c)
prettyCat  (Q a c)   = parens (prettyCat a <> text "?"    <> prettyCat c)
prettyCat  (RD a c)  = parens (prettyCat a <> text ">"    <> prettyCat c)
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
pn = FF (RD DP S) (BB DP S) -- abbreviation
ppn = FF (RD DP S) (BB pn S) -- abbreviation

lexicon =
  [("which",     ((FF (TN F (Q (FS DP N) S)) (BB (FS DP N) S)),   (make_var "which"))),
   ("the",       ((FF (TN F DP) (BB (FS DP N) S)),                (make_var "the"))),
   ("whose",     ((FF (TN F (BB pn S)) (BB pn S)),                (x^x))),
   ("friend-of", ((FS N DP),                                      (make_var "friend"))),
   ("crits-of",  ((FS N DP),                                      (make_var "crit"))),
   ("his",       ((FF (RD DP S) (BB DP S)),                       (x^x))),
   ("he",        ((FF (RD DP S) (BB DP S)),                       (x^x))),
   ("him",       ((FF (RD DP S) (BB DP S)),                       (x^x))),
   ("mother",    ((BS DP DP),                                     (make_var "mother"))),
   ("father",    ((BS DP DP),                                     (make_var "father"))),
   ("man",       (N,                                              (make_var "man"))),
   ("woman",     (N,                                              (make_var "woman"))),
   ("person",    (N,                                              (make_var "person"))),
   ("does",      ((FS S S),                                       (x^x))),
   ("that",      ((FS S S),                                       (x^x))),
   ("BIND",      ((FS (FF S (BB DP (RD DP S))) (FF S (BB DP S))), (f^g^(f#(x^(g#x#x)))))),
   ("everyone",  ((FF S (BB DP S)),                               (make_var "forall"))),
   ("someone",   ((FF S (BB DP S)),                               (make_var "exists"))),
   ("love",      ((FS (BS DP S) DP),                              (make_var "love"))),
   ("loves",     ((FS (BS DP S) DP),                              (make_var "loves"))),
   ("hates",     ((FS (BS DP S) DP),                              (make_var "hates"))),
   ("saw",       ((FS (BS DP S) DP),                              (make_var "saw"))),
   ("thinks",    ((FS (BS DP S) S),                               (make_var "thinks"))),
   ("gap_dp",    ((FF (BB DP S) (BB DP S)),                       (x^x))),
   ("gap_pn",    ((FF (BB pn S) (BB pn S)),                       (x^x))),
   ("gap_ppn",    ((FF (BB ppn S) (BB ppn S)),                       (x^x))),
   ("John",      (DP,                                             (make_var "j"))),
   ("Mary",      (DP,                                             (make_var "m"))),
   ("left",      ((BS DP S),                                      (make_var "left")))
  ]

go :: [String] -> Int -> [Edge]
go [] _ = []
go (word:tail) i = case lookup word lexicon of
                     Just (cat, sem) -> (Edge word cat sem i (i+1) "" []) : (go tail (i+1))
                     Nothing -> error ("\'" ++ word ++ "\' not found in lexicon.\n")

s1 = "which friend-of his mother does BIND everyone love gap_pn"
parse s =
    map (\x -> text "\n" <+> prettyEdge x)
        (filter (\(Edge _ _ _ l r _ _) -> ((r - l) == length(splitOn " " s)))
                (close findEdges (go (splitOn " " s) 0))
        )

-- parse "the friend-of his mother that BIND everyone saw gap_pn"
-- parse "the friend-of his whose crits-of his father BIND everyone hates gap_ppn"
