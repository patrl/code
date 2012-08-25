
(**state monad**)
type state = int list;;
let unit x = fun (s:state) -> (x, s);;
let unit' x = fun (s:state) -> (x, x::s);;

let bind x f = fun s -> 
  let (x', s') = x s in
  f x' s'
;;


(*some useful operations*)
let rec truthy list = match list with 
  | [] -> false
  | (a,b)::c -> if a then a else truthy c
;;

let rec clean_up list = match list with 
  | [] -> []
  | (a,b)::c -> if a then (a,b)::(clean_up c) else clean_up c
;;

let rec pop x list = match list with 
  | [] -> [x]
  | a::b -> if a = x then b@[x] else a::(pop x b)
;;

let tick m = bind m (fun x s -> 
  (x, pop x s))
;;


(**the model, lexical entries/primitives**)
let univ = [1;2;3;4;5;6;7;8;9;10];;

(*a trivial predicate*)
let thing x s = [bind x (fun y -> unit (y > 0 && y < 11)) s];;

(**lifting a relation into the monad w/L to R evaluation**)
let equals r l s = 
  [bind l (fun x -> 
    bind r (fun y -> 
      unit (x = y))) s]
;;

let gthan r l s = 
  [bind l (fun x -> 
    bind r (fun y -> 
      unit (x > y))) s]
;;

(*pronoun*)
let he = fun s -> (List.nth s 0, s);;
let he1 = fun s -> (List.nth s 1, s);;
let he2 = fun s -> (List.nth s 2, s);;

(*dynamic conjunction*)
let conj p q s = 
  let list1 = p s in
  let lift (a,b) q = if a then q b else [] in
  clean_up (List.concat (List.map (fun x -> x q) (List.map lift list1)))
;;

(*dynamic, testy negation*)
let neg p s = 
  let list1 = p s in
  if truthy list1 then [] else [(true, s)]
;;

(*dynamic, testy implication*)
let impl p q = neg (conj p (neg q));;

(*logical quantifiers*)
let forall p = 
  let rec checker list prop = match list with
    | [] -> true
    | a::b -> 
      if (prop a) = false 
      then false 
      else checker b prop in
  checker univ p
;;

(**quant determiners**)

let some p q s = 
  let test x =
    let extract p x q s =
      let list = p (unit x) s in
      let dref (a,b) = if a then [fun s -> (x,b@[x])] else [] in (*nb weirdness*)
      let extend = List.concat (List.map dref list) in
      List.concat (List.map (fun u -> q u s) extend) in
    let lift = extract p x q s in
    if truthy lift then lift else [] in
  List.concat (List.map test univ)
;;

let every p q s = 
  let test x =
    let extract p x q s =
      let list = p (unit x) s in
      let dref (a,b) = if a then [fun s -> (x,b@[x])] else [] in (*nb weirdness*)
      let extend = List.concat (List.map dref list) in
      List.concat (List.map (fun u -> q u s) extend) in
    let lift = extract p x q s in
    truthy (neg (p (unit x)) s) || truthy lift in
  if forall test then [(true, s)] else []
;;

(*???*)
let every' p q = neg (some p (fun x -> neg (q x)));;
(*seems to work as well*)

(*GQs*)
let eo = every thing;;
let so = some thing;;

(**in situ quantification and inverse scope**)

(*in-situ object quantifiers*)
let equals_lift q l = 
  bind l (fun l' s -> q (fun r -> equals r (unit l')) s);; 

let equals_ss o s = 
  s (fun l -> bind l (fun l' -> o (fun r -> bind r (fun r' s -> [(l'=r', s)]))));; 

let equals_ws o s = 
  o (fun r -> s (fun l -> equals_ss (fun f -> f r) (fun f -> f l)));;

(****
     THINGS IN A-POSITIONS PASS DREFS, LEFT TO RIGHT 
     (CF. BURING, THO DIFF)
****)


(*
  scope alternations of 'someone = everyone', nonrestricted, restricted versions 
  [false on SS, true on IS]
*)

so (equals_lift eo) [];;
equals_ws eo so [];;

equals_ss eo so [];;
equals_ss so eo [];;
equals_ws so eo [];;
equals_ws eo so [];;


(*regular binding ok: 'every x = x'*)
eo (equals he) [];;

(*strong crossover violations despite scope inversion*)
let he' p = p he;;

(*
  x = every x
  equals_lift eo he [];;
  equals_ws eo he' [];;

  # Exception: Failure "nth".
*)

(**weak crossover**)

(*first some acceptable examples: 'every x = (every/some y=x)'*)
eo (equals_lift (every (equals he))) [];;
eo (equals_lift (some (equals he))) [];;

(* 
   'every/some y=x = every x'
   equals_ws eo (every (equals he)) [];;
   equals_ws eo (some (equals he)) [];;
   
   # Exception: Failure "nth".
*)

(*
  roofing (natch): no inverse scope for 'every x = (some y=x)'
  equals_ws (some (equals he)) eo [];; 
  
  # Exception: Failure "nth".
*)

(*
  interestingly, wide-scoping a scope-taking (i.e. lifted) 
  pronoun without quantificational side effects just leads 
  to reconstruction and subsequent binding as if the pronoun 
  hadn't wide-scoped
*)
equals_ws he' eo [];;

(*
  cf. a case where the wide-scoped thing is a quantifier
  equals_ws (some (equals he)) eo [];;

  # Exception: Failure "nth".
*)


(**wco in extraction**)

(*gaps take scope*)
let gap p x = p (tick x);;

every (gap (equals he)) thing [];;
every (gap (equals_lift (some (equals he)))) thing [];;

(*
  gaps allow i-within-i, without them the determiner can't bind into its restrictor

  every (equals he) thing [];;
  
  # Exception: Failure "nth".
*)

(*
  crossover: the gap must precede the pronoun to be bound
  every (equals_ws gap he') thing  [];;
  every (equals_ws gap (some (equals he))) thing  [];;
  
  # Exception: Failure "nth".
*)

(*
  note also that it only makes semantic sense to give 
  a gap widest scope. 
  
  equals_lift gap he;;
  eo (equals_lift gap);;
  
  # type errors
*)

(*
  two gaps IS possible. wrong for english, but some languages
  do have multiple extraction.
*)

equals_ws gap gap;;
equals_ws gap gap he (unit 2) [];;
(*note to self: twice on stack, why?*)

(*?? why no good
equals_ss gap gap (unit 2) he [];;
*)

(**inverse-linking-style BOOD is derived, given a method for quantifying into DP. c-command isn't relevant for binding in the fragment---binding information is just passed left to right---cf. the following. [also, can keep DP as scope island]**)

(*simple non-c-command, non-scope binding out of DP; NL counterpart: sloppy ellipsis with DP-embedded antecedents*)
let g2 = gthan (unit' 2);;

some g2 (equals he) [];; (*i.e. some n>2 = 2 [false]*)

(*quantifying into DP; could do with QR or Hendriks -- barker/shan?*)
let gthanor10 r l s = 
  [bind l (fun x -> 
    bind r (fun y -> 
      unit (x > y || x = 10))) s];;

let dp1 x = some (gthanor10 x);;
let ar_dp = fun q p -> q (fun x -> dp1 x p);;
let dp2 = ar_dp eo;;


let gthan_lift q l s = 
  [bind l (fun l' s -> q (fun r -> gthan r (unit l')) s) s];; 
let gthit = gthan he;;

(*for every n, there is an m:m>n||m=10 s.t. m=m/m=n*)
dp2 (equals he1) [];;
dp2 (equals he) [];;

(*for every n, there is an m:m>n||m=10 s.t. m=some o=m/o=n*)
dp2 (equals_lift (some (equals he1))) [];;
dp2 (equals_lift (some (equals he))) [];;


(*relatedly we derive secondary crossover*)

(*
  equals_ws (some g2) he' [];;
  equals_ws dp2 he' [];;
  equals_ws (some g2) (some (equals he)) [];;
  equals_ws dp2 (some (equals he)) [];;
  # Exception: Failure "nth".
*)


(**crossover in questions**)

(*assume trace takes scope, giving a property to which wh-phrase attaches*)
let who f = f;;
let clause1 = gap (equals_lift he');;
let clause2 = gap (equals_lift (some (equals he)));;
who clause1 (unit 1) [];;
who clause2 (unit 1) [];;

(*
  failure when gap follows binder

  let clause' = equals_ws gap he';;
  who clause' (unit 1) [];;

  # Exception: Failure "nth".
*)


(**
   Reconstruction using CFs, which allow the restrictor
   to be evaluated in situ. Note: a similar trick is available
   for quantificational restrictors (a la Barker 2002)---i.e.
   we quantify over CFs, not individuals. This would enable a
   simplification of some of the apparatus (in particular equals_lift),
   but I've no idea how to teach a computer to quantify over all
   possible functions of a certain type...
**)

let the_least p s = 
  let rec checker list = match list with a::b ->
    if truthy (p (unit a) s) 
    then (a, s) 
    else checker b in
  checker univ;;

let which p q = fun f -> q (f p);;

(*
  which of its equals does every number equal? the least!
*)

which (equals he) (equals_ws gap eo) (the_least) [];;

(*
  binding into the answer
*)

let the_least_eq_it p s = 
  let rec checker list = match list with a::b ->
    let s1 = p (unit a) s in
    let s2 = equals he (unit a) s in
    if truthy s1 && truthy s2 then (a, s)
    else checker b in
  checker univ;;

(*
  which of its equals does every number equal? the least one equal to it!
*)

which (equals he) (equals_ws gap eo) (the_least_eq_it) [];;


(*
  reversing the position of gap and quantifier ~> crossover violation
  e.g. *which of its equals equals every number?

  which (equals he) (equals_ss eo gap) (the_least) [];;
  which (equals he) (equals_ss eo gap) (the_least_eq_it) [];;

  # Exception: Failure "nth".
*)


(**illustrating dynamic properties**)

(*
  some examples illustrating how conjunction works
  basically inspired by DPL/CDRT.
*)


conj (so thing) (so (gap (equals he))) [];;
conj (so thing) (so (gap (equals he1))) [];;
conj (so thing) (so (equals_ws gap he')) [];;

(*
  weak crossover violation in the second... 
  only one dref available at processing time.

  conj (so thing) (so (equals_ws gap (fun p -> p he1))) [];;

  # Exception: Failure "nth".
*)

(*donkey binding in conditionals*)
impl (so (equals (unit 2))) (equals (unit 2) he) [];;

(*
  crossover
  impl (equals (unit 2) he) (so (equals (unit 2))) [];;
  
  # Exception: Failure "nth".
*)

(*donkey binding from restrictors*)
every (equals_ws gap so) (equals he) [];;
every (equals_ws gap so) (equals he1) [];;

(*
  donkey strong crossover
  equals_ws (every (equals_ws gap so)) he' [];;

  donkey weak crossover
  equals_ws (every (equals_ws gap so)) (some (equals he)) [];;

  # Exception: Failure "nth".
*)

(**donkey reconstruction**)

let the_least_eq x p s = 
  let rec checker list = match list with a::b ->
    let s1 = p (unit a) s in
    let s2 = equals x (unit a) s in
    if truthy s1 && truthy s2 then (a, s)
    else checker b in
  checker univ;;

(*
  which of its equals does every number(n) equal to some number(m) equal?
  the least one equal to it(n/m)!
*)
which (equals he) (equals_ws gap (every (equals_ws gap so))) (the_least_eq he1) [];;
which (equals he) (equals_ws gap (every (equals_ws gap so))) (the_least_eq he) [];;


(**inv linking reconstruction**)

(*
  which of its equals does an(n) equal of every number(m) equal?
  the least one equal to it(n/m)!
*)
let dp1' x = some (equals x);;
let ar_dp' = fun q p -> q (fun x -> dp1' x p);;
let dp2' = ar_dp' eo;;

which (equals he) (equals_ws gap dp2') (the_least_eq he1) [];;
which (equals he) (equals_ws gap dp2') (the_least_eq he) [];;


(**2 think about**)

(*islands/resets?*)
(*superiority?*)

(*is gap pruning generally ok? every list always has same length??*)

(*weak and strong, plurals*)
(*functional readings, subordination*)
(*principle B w/stack?*)

(*can pass up constants easily w/relevant tweak to negation*)
(*ellipsis*)
(*exc scoping indefs?*)
(*type-shifter that pointwise applies elements of a non-det set*)


type prop = state -> (bool * state) list;;

let pw (op:prop -> prop) (p:prop) : prop = fun s -> 
  let list1 = p s in 
  let lifted = List.map (fun pair s' -> [pair]) list1 in
  List.concat (List.map (fun f -> op f s) lifted)
;;


let neg_pw = pw neg;;

let prop : prop = fun s -> [(true, s@[3]); (false, s@[4]); (false, s@[6])];;
neg_pw prop [];;

(*selective binding: treating members that agree on nth member as equiv class*)
(*no donald duck????*)
(*still question of 'every'*)
(*cps transform for scope-shift?*)



(*when one is a scope-taking DP, cf. binding rule*)
let left_apply l r k = 
  l (fun l' -> bind l' (fun l'' -> r (fun r' -> k (r' (unit l'')))))
;;

let right_apply l r k = 
  l (fun l' -> r (fun r' -> bind r' (fun r'' -> k (l' (unit r'')))))
;;

(*otherwise*)
let la l r k = 
  l (fun l' -> r (fun r' -> k (r' l')))
;;

let ra l r k = 
  l (fun l' -> r (fun r' -> k (l' r')))
;;


(*scope dislacement*)
let l3 l r c = l (fun l' -> r (fun r' -> c (fun c' -> left_apply l' r' c')));;
let r3 l r c = l (fun l' -> r (fun r' -> c (fun c' -> right_apply l' r' c')));;
let la3 l r c = l (fun l' -> r (fun r' -> c (fun c' -> la l' r' c')));;
let ra3 l r c = l (fun l' -> r (fun r' -> c (fun c' -> ra l' r' c')));;
let low f c = f (fun f' -> c (f' (fun x -> x)));;

let lift x c = c x;;
let int_lift h c = h (fun x -> c (fun k -> k x));;

let v = (lift (lift equals)) in
let s = lift eo in
let o = lift (some (equals he)) in
low (l3 s (r3 v o)) (fun x -> x) [];;

(*
  crossover

  let v = (lift (lift equals)) in
  let s = lift (some (equals he)) in
  let o = int_lift eo in
  low (l3 s (r3 v o)) (fun x -> x) [];;
  
  roofing 

  let v = (lift (lift equals)) in
  let s = lift eo in
  let o = int_lift (some (equals he)) in
  low (l3 s (r3 v o)) (fun x -> x) [];;
  
*)

(*note how binding scope rules are necessary even without restrictors*)
left_apply so (lift (fun x -> neg (gthan (unit 5) x))) (fun x -> x) [];;

(*adding resets*)
(*less than straightforward to do islands in multistage setting*)
let reset f k = k (f (fun x -> x));;

(*you could get rid of right binding rule, have two rules for FA and a separate one when you want to pass binding info from an argument -- analogous to the bind type-shifter*)
(*there is still a redundancy - you can have binding in "everyone likes himself" type constructions because bind is build into lex entry for lex relations*)

(*could try removing completely, just doing binding with scope rules*)

let bind' x f = fun s -> 
  let (x', s') = x s in
  f x' s;;

let equals' r l s = 
  [bind' l (fun x -> 
    bind' r (fun y -> 
      unit (x = y))) s]
;;

let gthan' r l s = 
  [bind' l (fun x -> 
    bind' r (fun y -> 
      unit (x > y))) s]
;;

(*
equals' he (unit' 2) [];;
*)
left_apply (lift (unit' 2)) (right_apply (lift equals') he') (fun x -> x) [];;
left_apply eo (right_apply (lift equals') (some (equals' he))) (fun x -> x) [];;


(*
  donkey anaphora, scope inside DP requires lowering, 
  but still have the possibility of binding, cf. BS
*)

let ddp = every' (left_apply gap (right_apply (lift gthan') so) (fun x -> x));;
left_apply ddp (right_apply (lift gthan') (fun p -> p he1)) (fun x -> x) [];;

(*to think about: islands, DP as scope island*)
 
(*why he2 is defined?*)
(*why are these stacks so long?*)
(*probably need to think some more about formluation of gaps*)
(*on the other hand, who cares?*)
(*unclear role of tick*)
some (left_apply gap (right_apply (lift gthan') so) (fun x -> x)) thing [];;
some (equals_ss so gap) thing [];;

