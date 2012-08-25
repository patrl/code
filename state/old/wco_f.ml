(**state monad**)
type state = int list;;
let unit x = fun (s:state) -> (x,s);;
let unit' x = fun (s:state) -> (x,x::s);;

let bind x f = fun s -> 
  let (x',s') = x s in
  f x' s'
;;

let tick m = bind m (fun x -> (unit' x));;

(**the model, lexical entries/primitives**)
let univ = [1;2;3;4;5;6;7;8;9;10];;

(*lifting a relation into the monad w/L to R evaluation*)
let thing x = 
  bind x (fun y -> 
    unit (y > 0 && y < 11))
;;

let equals r l = 
  bind l (fun x -> 
    bind r (fun y -> 
      unit (x = y)))
;;

let gthan r l = 
  bind l (fun x -> 
    bind r (fun y -> 
      unit (x > y)))
;;

(*pronoun*)
let he = fun s -> (List.nth s 0, s);;

(*dynamic conjunction*)
let conj r l = bind l (fun p -> bind r (fun q -> unit (p && q)));;


(**choice functions**)

(*
  a n-cf returns the n-th smallest member of p, or some arbitrary
  member of p if p has fewer than n members. of course there are
  many more cfs that one could gerrymander, but no matter how many 
  more you add, you'll have equivalent results. note that we presuppose
  the non-emptiness of restrictors.
*)
let cf n p =
  let make_list p = 
    let test p x = 
      if p x then [x] else [] in
    List.concat (List.map (test p) univ) in
  let noo = make_list p in
  if List.length noo < n then List.nth noo 0 else
    List.nth noo (n - 1)
;;


(*
  this makes all the monadized cfs. it also grabs the binding information
  packed in the det's restrictor and passes it along with the chosen indiv. 
*)
let m_cfs = 
  let deputize p s = fun x -> fst (p (unit x) s) in 
  let f_m f p s = 
    let new_s = snd (p (unit (f (deputize p s))) s) in    (*p != []*)
    (f (deputize p s), new_s) in
  List.map f_m (List.map cf univ)
;;

(*quantifying over cfs*)
let exists p = 
  let rec checker list prop = match list with
      [] -> false
    | a::b -> 
      if (prop a) = true 
      then true 
      else checker b prop in
  checker m_cfs p
;;

let forall p = 
  let rec checker list prop = match list with
      [] -> true
    | a::b -> 
      if (prop a) = false 
      then false 
      else checker b prop in
  checker m_cfs p
;;

(*GQs*)
let some p q s = 
  let prop = fun f -> fst (q (tick (f p)) s) in
  let first = exists prop in
  (first,s)
;;

let every p q s = 
  let prop = fun f -> fst (q (tick (f p)) s) in
  let first = forall prop in
  (first,s)
;;

let eo = every thing;;
let so = some thing;;

(*everything/something equals itself*)
eo (equals he) [];;
so (equals he) [];;

(*everything/something equals 2*)
eo (equals (unit 2)) [];;
so (equals (unit 2)) [];;


(**in situ quantification and inverse scope**)

(*in-situ object quantifiers*)
(*simpler than before, thanks to the cf approach*)
let equals_lift q l = q (fun r -> equals r l);; 

let equals_ws r l = 
  r (fun r' -> l (fun l' -> equals r' l'));; (*inverse scope*)

let equals_ss r l = 
  l (fun l' -> r (fun r' -> equals r' l'));; (*surface scope*)

(*
  scope alternations of 'someone = everyone', nonrestricted, restricted versions 
  [false on SS, true on IS]
*)

so (equals_lift eo) [];;
equals_ws eo so [];;


(**binding and crossover*)

(*regular binding ok: 'every x = x'*)
eo (equals he) [];;


(*strong crossover violations despite scope inversion*)
let he' p = p he;;

(*
  'x = every x'
  
  equals_lift eo he [];;
  equals_ws eo he' [];;

  # Exception: Failure "nth".
*)


(*weak crossover*)

(*first some acceptable examples: 'every x = (every/some y=x)'*)
let eqit = equals he;;
eo (equals_lift (every eqit)) [];;
eo (equals_lift (some eqit)) [];;

(* 
   'every/some y=x = every x'
   equals_ws eo (every eqit) [];;
   equals_ws eo (some eqit) [];;
   
   # Exception: Failure "nth".
*)


(*
  roofing derived: no inverse scope for 'every x = (some y=x)'
  i.e. i think the following is equivalent to narrow scope
  hence its truth. need to think more about these.
*)
equals_ws (some eqit) eo [];; 
  

(*
  interestingly, wide-scoping a scope-taking (i.e. lifted) 
  pronoun without quantificational side effects just leads 
  to reconstruction and subsequent binding as if the pronoun 
  hadn't wide-scoped
*)
equals_ws he' eo [];;


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
  every (equals_ws gap (some eqit)) thing  [];;
  every (equals_lift gap he) thing [];;
  
  # Exception: Failure "nth".
*)

(*
  note also that it only ever makes semantic sense to give 
  a gap widest scope over a quantifier.
  
  eo (equals_lift gap);;
  
  # type error
*)

(*
  two gaps IS possible. wrong for english, but some languages
  do have multiple extraction.
*)

equals_ws gap gap;;
equals_ws gap gap he (unit 2) [];;
equals_ss gap gap (unit 2) he [];;
(*note to self: twice on stack, why?*)


(**inverse-linking-style BOOD is derived, given a method for quantifying into DP. c-command isn't relevant for binding in the fragment---binding information is just passed left to right---cf. the following. [also, can keep DP as scope island]**)

(*simple non-c-command, non-scope binding out of DP; NL counterpart: sloppy ellipsis with DP-embedded antecedents*)
let g2 = gthan (unit' 2);;

some g2 (equals he1) [];; (*i.e. some n>2 = 2 [false]*)
(*figure out why it's in a different slot?*)

(*quantifying into DP; could do with QR or Hendriks -- barker/shan?*)
let gthanor10 r l = 
  bind l (fun x -> 
    bind r (fun y -> 
      unit (x > y || x = 10)));;

let dp1 x = some (gthanor10 x);;
let ar_dp = fun q p -> q (fun x -> dp1 x p);;
let dp2 = ar_dp eo;;

let he1 = fun s -> (List.nth s 1, s);;

let gthan_lift q l = 
  bind l (fun l' s -> q (fun r -> gthan r (unit l')) s);; 
let gthit = gthan he;;

(*for every n, there is an m:m>n||m=10 s.t. m=m/m=n*)
dp2 (equals he) [];;
dp2 (equals he1) [];;

(*for every n, there is an m:m>n||m=10 s.t. m=some o=m/o=n*)
dp2 (equals_lift (some (equals he))) [];;
dp2 (equals_lift (some (equals he1))) [];;


(*relatedly we derive secondary crossover*)

(*
  equals_ws (some g2) he' [];;
  equals_ws dp2 he' [];;
  equals_ws (some g2) (some eqit) [];;
  equals_ws dp2 (some eqit) [];;
  
  # Exception: Failure "nth".
*)


(*crossover in questions*)
(*assume trace takes scope, giving a property to which wh-phrase attaches*)
let who f = f;;
let clause1 = gap (equals_lift he');;
let clause2 = gap (equals_lift (some eqit));;
who clause1 (unit 1) [];;
who clause2 (unit 1) [2];;
(*note to self: 1 gets added to the stack here because of reformulation of gap*)
(*but not in second case because "some" is formulated as a test, and it takes widest scope*)

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
    let (bool, s) = p (unit a) s in
    if bool then (a, s) else
      checker b in
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
    let (bool1, s1) = p (unit a) s in
    let (bool2, s2) = equals he (unit a) s in
    if bool1 && bool2 then (a, s)
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
    


(*
  needed: donkey binding
*)

(*
it's actually already possible to do donkey binding the brasoveanu way; we just more or less put SETS on the stack, which aren't themselves bound into. so the dref contributed by "some thing" is the set of things. then the singular pronoun looks out at this set and picks a member, or possibly does something fancier like inducing an existential quantification. there is obviously some fancier stuff going on in adrian's system. but the basic appraoch is emulable. 

the approach is also similar in some ways to the way mike "delays witness selection" to account for weak and strong readings. 

in principle, you could also extend this to the kinds of ellipsis and exceptional scope cases i was worried about, but it would require slightly more complex entries for "every" and "some" which were more discriminate about binding information (currently they're consummate tests). for e.g. wide-scope indefinites, you could have an existential closure operator that looks at a set on the stack and existential quantifies over it.

it would be interesting to see what happens with roofing when wide scope indefinites are handled in this way.
 
in the end, you'd have an account where donkey anaphora and exceptional scope are each possible because of the dynamic binding apparatus. 
*)


(*principle B w/stack, islands/resets?*)




(*DE*)
let no p q s = 
  let prop = fun f -> fst (q (tick (f p)) s) in
  let first = not (exists prop) in
  (first,s)
;;

let leq r l = 
  bind l (fun x -> 
    bind r (fun y -> 
      unit (x <= y)))
;;

let gthan_ws r l = r (fun r' -> l (fun l' -> gthan r' l'));;
let gthan_ss r l = l (fun l' -> r (fun r' -> gthan r' l'));;
let gthan_lift r l = r (fun r' -> gthan r' l);;

gthan_ws (some (leq he)) (no thing) [];;
gthan_ss (some (leq he)) (no thing) [];;

gthan_ws (some (equals he)) (no thing) [];;
gthan_ss (some (equals he)) (no thing) [];;

gthan_ws (every (leq he)) (no thing) [];; (*wrong*)
gthan_ss (every (leq he)) (no thing) [];;
no thing (gthan_lift (every (leq he))) [];; 

so (gthan_lift (every (leq he))) [];; 
gthan_ws (every (leq he)) so [];; (*wrong*)


(*rel to functional readings?*)
(*presuppositions assoc w/restrictors project universally?*)
