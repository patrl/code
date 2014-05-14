import Debug.Trace
import Text.PrettyPrint

data Conn = BS | FS | BB | FF deriving (Eq, Show)
data For = DP | N | S | E | Q | For Conn For For | Box For | Dia For
           deriving (Eq, Show)
data Mod = Merge | Cont deriving (Eq, Show)
data Structure =   Leaf Term For
                 | Hole Int
                 | Lam Int Structure
                 | Branch Mod Structure Structure
                 | Unary Structure
                 | F | I | B | C 
                 deriving (Eq, Show) 
data Context =   Null 
               | Lamcon Int Context
               | Unarycon Context
               | Lcon Mod Context Structure 
               | Rcon Mod Structure Context deriving (Eq, Show)

focus :: Structure -> [(Structure, Context)]
focus (Branch m l r) = 
     [(t, (Lcon m c r)) | (t, c) <- focus l]
  ++ [(t, (Rcon m l c)) | (t, c) <- focus r]
  ++ [(Branch m l r, Null)]
focus (Lam i s) =    [(t, (Lamcon i c)) | (t, c) <- focus s]
                  ++ [(Lam i s, Null)]
focus (Unary s) =    [(t, (Unarycon c)) | (t, c) <- focus s] 
                  ++ [(Unary s, Null)]
focus t = [(t, Null)]

plug :: Structure -> Context -> Structure
plug t Null = t
plug t (Lamcon i c) = Lam i (plug t c)
plug t (Unarycon c) = Unary (plug t c)
plug t (Lcon m c r) = Branch m (plug t c) r
plug t (Rcon m l c) = Branch m l (plug t c)

reduce :: Structure -> Structure -> Structure
reduce p (Lam i (Hole i')) = if i == i' then p else (Hole i')
reduce p (Lam i (Lam j q)) = if i == j then (Lam j q) else (Lam j (reduce p (Lam i q)))
reduce p (Lam i (Branch m l r)) = Branch m (reduce p (Lam i l))
                                           (reduce p (Lam i r))
reduce p (Lam i q@(Leaf _ _)) = q
reduce p q = q

noBB :: Structure -> Bool
noBB (Branch m B B) = False
noBB (Branch m p q) = and [noBB p, noBB q]
noBB (Lam _ p) = noBB p
noBB _ = True

noUnary :: Context -> Bool
noUnary (Unarycon _) = False
noUnary (Lamcon _ c) = noUnary c
noUnary (Lcon _ c r) = noUnary c
noUnary (Rcon _ l c) = noUnary c
noUnary _ = True

lamtoibc :: Structure -> Structure
lamtoibc (Lam i (Hole _)) = I
lamtoibc (Lam i (Lam j q)) = lamtoibc (Lam i (lamtoibc (Lam j q)))
lamtoibc (Lam i (Branch m l r)) = 
  if (free i l) then Branch m (Branch Merge B l) (lamtoibc (Lam i r)) 
                else Branch m (Branch Merge C (lamtoibc (Lam i l))) r 
lamtoibc p = p

free :: Int -> Structure -> Bool
free i (Hole i') = if i == i' then False else True
free i (Lam j q) = if i == j then True else free i q
free i (Branch m l r) = and [free i l, free i r]
free i _ = True

data Sequent = Seq Structure For deriving (Eq, Show)

data Proof =   Axiom Sequent 
             | Beta Proof Sequent
             | R Conn Proof Sequent       -- R = Right rule
             | L Conn Proof Proof Sequent -- L = Left rule
     deriving (Eq, Show)

data Term = Word String | Var Int | Lambda Int Term | App Term Term 
            | Pair Term Term
            deriving (Eq, Show)

type History = [Sequent]

prove :: Sequent -> History -> [(Proof, Term)]
prove s@(Seq l r) history =

--   trace (show(prettySequent s)) [] ++

   if elem s history then [] else

   let ax = [(Axiom s, t) | Leaf t f <- [l], f == r] in
   if not (null ax) then ax else

   let i = length history in
   let agenda = focus l in 

   foldl (++) []
   [

   [(Beta x s, t) | ((Unary (Leaf t' (Box p))), cxt) <- agenda
       , (x, t) <- prove (Seq (plug (Leaf t' p) cxt) r) (s:history)],

   [(Beta x s, Lambda i (Pair t (Var i))) | Dia p <- [r]
      , (x, t) <- prove (Seq l p) (s:history)],

-- -------------------------------------------

   [(R BS x s, Lambda i t) | For BS a c <- [r]
      , (x, t) <- prove (Seq (Branch Merge (Leaf (Var i) a) l) c) (s:history)],

   [(R FS x s, Lambda i t) | For FS c b <- [r]
      , (x, t) <- prove (Seq (Branch Merge l (Leaf (Var i) b)) c) (s:history)],

   [(R BB x s, Lambda i t) | For BB a c <- [r]
      , (x, t) <- prove (Seq (Branch Cont (Leaf (Var i) a) l) c) (s:history)],

   [(R BB x s, Lambda i t) | For BB a c <- [r], Lam _ _ <- [l]
      , (x, t) <- prove (Seq (reduce (Leaf (Var i) a) l) c) (s:history)],

   [(R FF x s, Lambda i t) | For FF c b <- [r]
      , (x, t) <- prove (Seq (Branch Cont l (Leaf (Var i) b)) c) (s:history)],

   [(L BS x y s, t') | ((Branch Merge gamma (Leaf i' (For BS a b))), cxt) <- agenda
      , (x, t) <- prove (Seq gamma a) (s:history)
      , (y, t') <- prove (Seq (plug (Leaf (App i' t) b) cxt) r) (s:history)],

   [(L FS x y s, t') | ((Branch Merge (Leaf i' (For FS b a)) gamma), cxt) <- agenda
      , (x, t) <- prove (Seq gamma a) (s:history)
      , (y, t') <- prove (Seq (plug (Leaf (App i' t) b) cxt) r) (s:history)],

   [(L BB x y s, t') | ((Branch Cont gamma (Leaf i' (For BB a b))), cxt) <- agenda
      , (x, t) <- prove (Seq gamma a) (s:history)
      , (y, t') <- prove (Seq (plug (Leaf (App i' t) b) cxt) r) (s:history)],

   [(L FF x y s, t') | ((Branch Cont (Leaf i' (For FF b a)) gamma), cxt) <- agenda
      , (x, t) <- prove (Seq gamma a) (s:history)
      , (y, t') <- prove (Seq (plug (Leaf (App i' t) b) cxt) r) (s:history)],

   [(L FF x y s, t') | (foc, sigma) <- agenda, (Leaf i' (For FF b a), gamma) <- focus foc
      , noBB (lamtoibc (Lam i (plug (Hole i) gamma)))
      , noUnary gamma
      , (x, t) <- prove (Seq (Lam i (plug (Hole i) gamma)) a) (s:history)
      , (y, t') <- prove (Seq (plug (Leaf (App i' t) b) sigma) r) (s:history)]

   ]

-- --------------------------------------------------------------------------

test = let 
         pn = (For FF (For BB DP S) (For BB DP (For BB DP S)))
         vp = (For BS DP S)
         some = (Leaf (Word "some") (For FS (For FF S (For BB DP S))
                                            (For BS E S)))
         every = (Leaf (Word "every") (For FS (For FF S (For BB DP S))
                                            (For BS E S)))
         man = (Leaf (Word "man") N)
         city = (Leaf (Word "city") (For BS E S))
         from = (Leaf (Word "from") (For FS (For BS (For BS E S) 
                                                    (For BS E S)) 
                                            DP))
         friendOf = (Leaf (Word "friend of") (For FS N DP))

         his = (Leaf (Word "his")(For FF (For BB DP S) 
                                         (For BB DP (For BB DP S))))
         it = (Leaf (Word "his")(For FF (For BB DP S) 
                                        (For BB DP (For BB DP S))))
         mother = (Leaf (Word "mother") (For BS DP DP))
         thinks = (Leaf (Word "thinks") (For FS (For BS DP S) S))
         apparently = (Leaf (Word "apparently") (For FS S S))
         gap = (Leaf (Word "GAP") (For FF (For BB DP S) (For BB DP S)))  
         pngap = (Leaf (Word "PNGAP") (For FF (For BB pn S) (For BB pn S)))  
         left = (Leaf (Word "left") vp)
         john = (Leaf (Word "John") DP)
         mary = (Leaf (Word "Mary") DP)
         qdp = (For FF S (For BB DP S))
         someone = (Leaf (Word "someone") qdp)
         loves = (Leaf (Word "loves") (For FS (For BS DP S) DP))
         everyone = (Leaf (Word "everyone") qdp)
         read = (Leaf (Word "read") (For FS (For BS DP S) DP))
         the = (Leaf (Word "the") (For FS DP (For BS E S)))
         book = (Leaf (Word "book") N)
         rel = (Leaf (Word "rel") (For FS (For BS N (For BS E S)) (For BB DP S)))
         did = (Leaf (Word "did") (For FS S S))
         which = (Leaf (Word "which") (For FF Q (For BB (For FS DP N) S)))
         who = (Leaf (Word "who") (For FF Q (For BB DP S)))
         fin = (Leaf (Word "FIN") (For FS (Box (Dia S)) (Dia S)))
         chsomeone = (Leaf (Word "someone") (For FF (Dia S) (For BB DP (Dia S))))
         wants = (Leaf (Word "wants") (For FS vp vp))
         acegap = (Leaf (Word "ACEGAP") (For FF (For FF (For FF S (For BB vp S)) (For BB DP vp)) (For BB (For FS vp DP) qdp)))

      in 
         (\s -> 
           map (\(p, t) -> vcat [char ' ', prettyProof p, 
                                 char ' ', prettyTerm t])
               (take 2
                 (prove s []))
                )

-- (Seq (Unary (Branch Merge fin (Branch Merge chsomeone (Branch Merge loves chsomeone)))) (Dia S))
-- (Seq (Unary (Branch Merge fin (Branch Merge john left))) (Dia S))
-- (Seq (Branch Merge john left) (Dia S))
-- (Seq (Branch Merge (Unary (Leaf (Word "boxed-john") (Box DP))) left) S)
-- (Seq (Branch Merge (Branch Merge his mother) (Branch Merge loves everyone)) S)
-- (Seq (Branch Merge everyone (Branch Merge loves (Branch Merge his mother))) S)
-- (Seq (Branch Merge someone (Branch Merge loves everyone)) S)
-- (Seq (Branch Merge john (Branch Merge loves everyone)) S)
-- (Seq (Branch Merge everyone left) S)
-- (Seq (Branch Merge (Branch Merge every (Branch Merge book (Branch Merge rel (Branch Merge john (Branch Merge loves gap))))) left) S)


-- ACE examples

-- john loves every book john does
-- (Seq (Branch Merge john (Branch Merge loves (Branch Merge every (Branch Merge book (Branch Merge rel (Branch Merge john (Branch Merge acegap gap))))))) S)

-- john loves the book john does (notice that we end up needing to "lift" the object DP; does this have something to say about hackl's processing results?)
-- (Seq (Branch Merge john (Branch Merge loves (Branch Merge the (Branch Merge book (Branch Merge rel (Branch Merge john (Branch Merge acegap gap))))))) S)

-- someone loves every book john does (inverse scope possible!)
 (Seq (Branch Merge someone (Branch Merge loves (Branch Merge every (Branch Merge book (Branch Merge rel (Branch Merge john (Branch Merge acegap gap))))))) S)

-- john wants to love every book john does (i *think* the parser should allow for an ambiguity about where to resolve the ACD--i.e. above or below "wants"--but even taking 204, i can't get the parser to find it)
-- (Seq (Branch Merge john (Branch Merge wants (Branch Merge loves (Branch Merge every (Branch Merge book (Branch Merge rel (Branch Merge john (Branch Merge acegap gap)))))))) S)


vars = "xyz"++['a'..'w']
prettyTerm :: Term -> Doc
prettyTerm (Word s) = text s
prettyTerm (Var i) = char (vars!!i)
prettyTerm (Lambda i t) = parens (char '\\' <> char (vars!!i) <+> prettyTerm t)
prettyTerm (App t1 t2) = parens ((prettyTerm t1) <+> (prettyTerm t2))
prettyTerm (Pair t1 t2) = parens ((prettyTerm t1) <> text "," <+> (prettyTerm t2))

prettyConnective :: Conn -> Doc
prettyConnective (BS) = text "\\"
prettyConnective (FS) = text "/"
prettyConnective (BB) = text "\\\\"
prettyConnective (FF) = text "//"

prettyFormula, prettyFormula' :: For -> Doc
prettyFormula  (For op a c)  = prettyFormula' a <> prettyConnective op 
                                                <> prettyFormula' c
prettyFormula  (Box a) = text "[]" <> prettyFormula a
prettyFormula  (Dia a) = text "<>" <> prettyFormula a
prettyFormula  a             = text (show a)
prettyFormula' a@(For _ _ _) = parens (prettyFormula a)
prettyFormula' a             =         prettyFormula a

prettyStructure, prettyStructure' :: Structure -> Doc
prettyStructure  (Leaf _ t)   = prettyFormula t
prettyStructure  (Branch Merge  l r)   = prettyStructure' l <+> char '*'  
                                                   <+> prettyStructure' r
prettyStructure  (Branch Cont p c)   = prettyStructure' p <+> text "**" 
                                                   <+> prettyStructure' c
prettyStructure  (Lam i p) = text "\\" <> int i <> parens (prettyStructure p)
prettyStructure  (Hole i) = int i
prettyStructure  (Unary p) = text "<" <> prettyStructure p <> text ">" 
prettyStructure  s            = text (show s)
prettyStructure' s@(Branch Merge  _ _) = parens (prettyStructure s)
prettyStructure' s@(Branch Cont _ _) = parens (prettyStructure s)
prettyStructure' s            =         prettyStructure s

prettySequent :: Sequent -> Doc
prettySequent (Seq s a) = prettyStructure s <+> text "|-" <+> prettyFormula a

prettyProof :: Proof -> Doc
prettyProof (Axiom     s  ) = text "  " <> (prettySequent s) <> text " :Ax"
prettyProof (Beta x s)      = text "  " <> (prettyProof x 
                                $+$ prettySequent s) <> text " :b"
prettyProof (R c x s  )     = text "  " <> (prettyProof x $+$ prettySequent s)
                                <> text " :" <> prettyConnective c <> text "R"
prettyProof (L c x y s)     = text "  " <> (prettyProof x $+$ prettyProof y 
                                $+$ prettySequent s)
                                <> text " :" <> prettyConnective c <> text "L"

main = print test
