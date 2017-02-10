(*LEXICON*)
type state = int list;;
let unit x = fun (y:state) -> (x,y);;
let lift x = [unit x];;
let univ = [1;2;3;4;5;6];;
let dummy x p = if x = 0 then false else p;;
let man = fun x -> dummy x (if (x = 1 or x = 2 or x = 5) then true else false);;
let woman = fun x -> dummy x (if (x = 3 or x = 4) then true else false);;
let left = fun x -> dummy x (if (x = 2) then false else true);;
let smokes = fun z -> dummy z (if (z = 1 or z = 3 or z = 4) then true else false);;
let ran = fun x -> dummy x (if (x = 1 or x = 4) then true else false);;
let french = fun z -> dummy z (if (z = 2 or z = 6) then false else true);;
let loves = fun x -> fun y -> dummy x (dummy y (if y > x then true else false));;
let rec even n = if n = 0 then true else 
    if (n - 1) = 0 then false else
      even (n-2);;
let sees x y = dummy x (dummy y (if even x & even y then true else false));;
let kisses x y = dummy x (dummy y (if ((y - x) > 1) then true else false));;
let meets x y = dummy x (dummy y (if (abs (y - x)) < 3 then true else false));;

(*LOWERING*)
let spurious (a,b) = 
  let rec found n list = match list with
      [] -> false 
    | a::b -> 
      if a = n 
      then true 
      else found n b in
  found 0 b;;
let rec trooths list = match list with 
    [] -> []
  | a::b -> 
    if (fst a = false or spurious a) then trooths b 
    else a::trooths b;;
let lower list = trooths (List.map (fun pair -> pair []) list);;

(*PLUMBING*)
let bind m k x =
  let (a,y) = m x in
  let (b,z) = k a y in
  (b,z);;

(*dynamic function application. NB: this gives drefs in the argument scope over those in the functor---though p outscopes q in dynfa, this means p's drefs are added to the state first; q's drefs are added on top of these. this means pronouns in the functor won't have access to drefs in the argument---this is easy (though tedious) to fix. once that happens, though, intrasentential binding will depend on c-command!*)
let dynfa p q =
  [bind p (fun x -> (
    bind q (fun y -> (
      unit (x y)))))];;

(*dynamic conjunction. NB: assuming "and" takes its right argument first, this entry gives drefs in the right conjunct "scope" over those in the left conjunct (i.e. they're further left in the list). crucially, however, it makes drefs in the left conjunct accessible to those in the right conjunct.*)
let dynand p q =
  [bind q (fun x -> (
    bind p (fun y -> (
      unit (x & y)))))];;

(*dynamic disjunction. only externally dynamic--and then, only if each disjunct contributes a dref*)
let dynor list1 list2 = List.concat [list1; list2];;

let pointwise op f a = 
  List.concat (List.map (fun g -> List.concat (List.map g a)) (List.map op f));;
  
let a np =
  let uni = List.concat (List.map lift univ) in 
  let statefa p q = bind p (fun x -> (bind q (fun y -> (unit (x y))))) in
  let drefs = fun f a -> [fun g ->  
    let (c,d) = statefa f a g in 
    let dref = fst(a g) in
    if c = true 
    then (dref,dref::d)
    else (0,0::d)] in
  pointwise drefs np uni;;

let he n = [fun g -> (List.nth g (n-1), g)];;
let she n = [fun g -> (List.nth g (n-1), g)];;

let amanleft = pointwise dynfa (lift left) (a (lift man));;
lower amanleft;;
let awomansmokes = pointwise dynfa (lift smokes) (a (lift woman));;
lower awomansmokes;;
let hesmokes = pointwise dynfa (lift smokes) (he 1);;
let amansmokes = pointwise dynfa (lift smokes) (a (lift man));;
let heran = pointwise dynfa (lift ran) (he 1);;
let aman = a (lift man);;
let awoman = a (lift woman);;
let lovesawoman = pointwise dynfa (lift loves) (awoman);;

(*a woman loves a man*)
(*the true pairs give all the pairings of women with men they love---i.e. >.*)
let awomanlovesaman = pointwise dynfa (pointwise dynfa (lift loves) aman) awoman;;
lower awomanlovesaman;;

(*a man loves a woman*)
(*the true pairs give all the pairings of men with women they love---i.e. >.*)
let amanlovesawoman = pointwise dynfa (pointwise dynfa (lift loves) (awoman)) aman;;
lower amanlovesawoman;;

(*a man left. he smokes*)
(*the true pairs give all the men who smoke*)
let amanlefthesmokes =  pointwise dynand hesmokes amanleft;;
lower amanlefthesmokes;;

(*a man left. a woman smokes*)
(*the true pairs give all the pairings of men who left and women who smoke*)
let amanleftawomansmokes =  pointwise dynand awomansmokes amanleft;;
lower amanleftawomansmokes;;

(*a man left, or a woman smokes*)
(*the true pairs have a man who left or a woman who smokes*)
let amanleftorawomansmokes = dynor awomansmokes amanleft;;
lower amanleftorawomansmokes;;

(*a man left, or a woman smokes. s/he ran*)
(*stone's problem is no problem here*)
lower (pointwise dynand heran amanleftorawomansmokes);;

(*a man loves a woman. a woman loves a man*)
lower (pointwise dynand awomanlovesaman amanlovesawoman);;

(*an entry for "not" that percolates alternatives, ~> wide scope, cf. mascarenhas on PPIs. important for the lexical entry to contain "spurious" here since otherwise the false claims associated with the spurious dref "0" will have their polarity reversed.*)
let nought list = List.map (fun point g -> if (spurious (point g) or fst(point g) = true) then (false, snd(point g)) else (true, snd(point g))) list;;

lower (nought (pointwise dynfa (lift left) (a (lift man))));;

(*an entry for "not" that obliterates alternatives---i.e. is externally static. vastly improved over the previous version*)
let nah p = [fun g ->
  let perset = List.map (fun po -> po g) in
  if trooths (perset p) = []
  then (true, g)
  else (false, g)];;

(*a woman smokes. no man left*) 
lower (pointwise dynand (nah amanleft) awomansmokes);;

(*a woman smokes. no man is a woman.*)
let amanwoman = pointwise dynfa (lift woman) (a (lift man));;
lower (pointwise dynand (nah amanwoman) awomansmokes);;

(*a man smokes. he doesn't love a woman.*)
lower (pointwise dynand (nah (pointwise dynfa lovesawoman (he 2))) amansmokes);;

(*a man left. he doesn't love a woman.*)
lower (pointwise dynand (nah (pointwise dynfa lovesawoman (he 2))) amanleft);;

(*a better entry for "not" enables a vastly improved entry for "if"*)
let iffy p q = nah (pointwise dynand (nah q) p);;

let hefrench = pointwise dynfa (lift french) (he 1);;
lower (iffy amansmokes heran);;
lower (iffy amanleft heran);;
lower (iffy amanleftorawomansmokes hefrench);;

let shekisseshim = pointwise dynfa (pointwise dynfa (lift kisses) (he 2)) (she 1);;
let hekissesher = pointwise dynfa (pointwise dynfa (lift kisses) (she 2)) (he 1);;
let sheloveshim = pointwise dynfa (pointwise dynfa (lift loves) (he 2)) (she 1);;
let helovesher = pointwise dynfa (pointwise dynfa (lift loves) (she 2)) (he 1);;
let heseesher = pointwise dynfa (pointwise dynfa (lift sees) (she 2)) (he 1);;
let hemeetsher = pointwise dynfa (pointwise dynfa (lift meets) (she 2)) (he 1);;
let shemeetshim = pointwise dynfa (pointwise dynfa (lift meets) (he 1)) (she 2);;
let shekisseshim = pointwise dynfa (pointwise dynfa (lift kisses) (he 1)) (she 2);;

(*if a woman loves a man she {kisses, loves} him*)
lower (iffy awomanlovesaman shekisseshim);;
lower (iffy awomanlovesaman sheloveshim);;

(*if a man loves a woman he {kisses, loves, meets, sees} her*)
lower (iffy amanlovesawoman hekissesher);;
lower (iffy amanlovesawoman helovesher);;
lower (iffy amanlovesawoman hemeetsher);;
lower (iffy amanlovesawoman heseesher);;

(*if a man loves a woman SHE {meets, kisses} HIM*)
lower (iffy amanlovesawoman shemeetshim);;
lower (iffy amanlovesawoman shekisseshim);;

(*dynamic binding out of restrictor*)
(*relative pronoun*)
let who np1 np2 =
  [bind np2 (fun x -> (
    bind np1 (fun y -> (
      unit (fun z -> (x z) & (y z))))))];;

(*an entry for "every". internally dynamic: puts "every"'s dref on the stack, passes it and the indefinite drefs to dynamic implication. outputs an empty stack when fed the trivial continuation.*)
let every np vp = [fun g ->
  let forallx p = 
    let rec checker list prop = match list with
	[] -> true
      | a::b -> 
	if (prop a) = false 
	then false 
	else checker b prop in
    checker univ p in
  let pred np vp = fun x -> 
    let p = [fun g -> (x,x::g)] in
    let perset = List.map (fun po -> po g) in
    not (trooths (perset (iffy (pointwise dynfa np p) (pointwise dynfa vp p))) = []) in
    (forallx (pred np vp),g)];;

(*every man who loves a woman {loves, sees, meets} her*)
let lovesher = pointwise dynfa (lift loves) (she 2);;
let seesher = pointwise dynfa (lift sees) (she 2);;
let meetsher = pointwise dynfa (lift meets) (she 2);;
lower (every (pointwise who (lovesawoman) (lift man)) (lovesher));;
lower (every (pointwise who (lovesawoman) (lift man)) (seesher));;
lower (every (pointwise who (lovesawoman) (lift man)) (meetsher));;

(*every man {meets, loves} a woman. obliterates alternatives. but want a wide-scope reading too. necessitates another entry for "every"*)
let meetsawoman = pointwise dynfa (lift meets) (a (lift woman));;
lower (every (lift man) meetsawoman);;
lower (every (lift man) lovesawoman);;

(*every man meets himself*)
let meetshim = pointwise dynfa (lift meets) (he 1);;
lower (every (lift man) meetshim);;

(*every man who loves a woman meets himself*)
lower (every (pointwise who (lovesawoman) (lift man)) meetshim);;
