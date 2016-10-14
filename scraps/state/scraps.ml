
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

type state = int list;;
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

  CRO
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


(*could try removing completely from lexical meanings, then doing binding exclusively with scope rules*)

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
left_apply ddp (right_apply (lift gthan') (fun p -> p he)) (fun x -> x) [];;

(*to think about: islands, DP as scope island*)
 
(*why he2 is defined?*)
(*why are these stacks so long?*)
(*probably need to think some more about formluation of gaps*)
(*on the other hand, who cares?*)
(*unclear role of tick*)
some (left_apply gap (right_apply (lift gthan') so) (fun x -> x)) thing [];;
some (equals_ss so gap) thing [];;

(*inverse linking with these rules*)
low (l3 (ra (lift some) (right_apply (lift equals') eo)) (lift (lift thing))) (fun x -> x) [];;
(*to what does DP as scope island correspond _?*)

(*problem with gap*)
ra (lift some) (ra (lift gap) (right_apply (lift gthan') eo));;
low (l3 (ra (lift some) (la gap (right_apply (lift equals') eo))) (lift (lift thing))) (fun x -> x) [];;
low (l3 (ra (lift some) (ra (lift gap) (right_apply (lift equals') eo))) (lift (lift thing))) (fun x -> x) [];;


(*superiority*)
(*who _ loves what*)
(*what does who love _*)
(*traces introduce functional dependency for us too*)
(*also notice that you cant scope certain things under certain ops*)

(*wh- pied piping*)
let who' f x = f (tick x);;
let succ' x = bind' x (fun x' -> unit (succ x'));;


(*whose successor is greater than it? 2's! (inter alia!)*)
left_apply (left_apply who' (lift succ')) (ra (lift gthan') (some (equals' he))) (fun x -> x) (unit 2) [];;
la (left_apply who' (lift succ')) (ra (lift gthan') (some (equals' he))) (fun x -> x) (unit 2) [];;

(*
  always must apply binding rule to binding DP!
  
  left_apply (la who' (lift succ')) (ra (lift gthan') (some (equals' he))) (fun x -> x) (unit 2) [];;
*)

(*posessive BOOD*)
(*everyone's successor > it/some n=it*)
la (left_apply eo (lift succ')) (ra (lift gthan') he') (fun x -> x) [];;
la (left_apply eo (lift succ')) (ra (lift gthan') (some (equals' he))) (fun x -> x) [];;


(*
  can only bind into saturated stuff?
  
  left_apply who' (right_apply (lift equals) who);;
  left_apply who (right_apply (lift equals) who);;

  good because ken's wrong about pair-list binding?

*)

la who (right_apply (lift equals) who) (fun x -> x);;

(la who' (right_apply (lift gthan') gap) (fun x -> x)) (unit 3) (unit 2) [];;
(la gap (right_apply (lift gthan') who') (fun x -> x)) (unit 3) (unit 2) [];;


(who' (la who' (right_apply (lift gthan') gap) (fun x -> x))) (unit 3) (unit 2) [];;
(who' (la gap (right_apply (lift gthan') who') (fun x -> x))) (unit 3) (unit 2) [];;

(*no good for wh in situ?*)
(*rather, requires L wh phrase to be in situ*)
(*moved wh-phrases don't combine via continuation mode!*)
(*cf chris*)
(*requires lowering*)
who (left_apply gap (right_apply (lift equals') he') (fun x -> x)) (unit 4) [];;
eo (who (left_apply gap (right_apply (lift equals') he') (fun x -> x))) [];;

(*can they do surface scope inverse linking without a propertytype lower/3 level tower*)

(*can do VP shells data too*)

let sum7 x y z = bind' x (fun x' -> bind' y (fun y' -> bind' z (fun z' s -> [unit (x'+y'+z'=7) s])));;

left_apply (fun p -> p (unit 3)) (ra (right_apply (lift sum7) so) (some (equals' he))) (fun x -> x) [];;

(*wine before its time*)


(**application of x_apply to DPs forces immediate evaluation, la doesn't**)
let bind_et f g = 
(*lift*)
fun p -> p (fun x -> bind' x (fun x' s -> [unit (x' = 10)]));;


(*
let left_apply l r k = 
  l (fun l' -> bind (fun s -> ((), s@[l'])) (fun () -> r (fun r' -> k (r' l'))))
;;
*)


low (la3 (l3 (lift he') (lift (lift succ'))) (r3 (lift (lift gthan')) (int_lift eo))) (fun x -> x) [];;


let he_ f = he' (fun l' -> bind l' (fun l'' -> f (unit l'')));;
let eo_ f = eo (fun l' -> bind l' (fun l'' -> f (unit l'')));;
let eo__ c = eo (fun x -> c (fun k -> bind x (fun x' -> k (unit x'))));;

low (la3 (lift he_) (ra3 (lift (lift equals')) (int_lift eo_))) (fun x -> x ) [];;

let int_lift_ h c s = h (fun x s' -> c (fun k -> bind x (fun x' -> k (unit x'))) s) s;;

low (l3 (lift he') (r3 (lift (lift equals')) (int_lift eo))) (fun x -> x) [];;



let eo__ c = eo (fun x -> c (fun k -> bind x (fun x' -> k (unit x'))));;

low (la3 (lift he_) (ra3 (lift (lift equals')) eo__)) (fun x -> x) [];;
low (la3 eo__ (ra3 (lift (lift equals')) (lift he_))) (fun x -> x) [];;

(*apply bind only to quantifiers*)
(*pronouns just mean he_*)

(*int lift after you apply to a q subverts co*)
(*so we need an int lift that leaves binding info downstairs*)
(*the question: what's the relation between eo_ and eo__?*)
(*if we get this, we can just have la and ra*)

low (la3 (int_lift_ eo) (lift (right_apply (lift equals') he_))) (fun x -> x) [];;
low (la3 (lift he_) (int_lift_ (right_apply (lift equals') eo))) (fun x -> x) [];;
low (la3 (lift he') (r3 (lift (lift equals')) (int_lift eo))) (fun x -> x) [];;
low (la3 (lift he_) (r3 (lift (lift equals')) (int_lift_ eo))) (fun x -> x) [];;

low (la3 (lift he_) (int_lift (right_apply (lift equals') eo))) (fun x -> x) [];;
low (la3 (lift he_) (r3 (lift (lift equals')) (int_lift eo))) (fun x -> x) [];;

(*
  working combos:

  -he_, eo, int_lift only applies to DPs, need x_apply
  -always apply x_apply to pronouns, int_lift only DPs
  -he_, eo_, only xa, int_lift_ (type error when applies to e.g. VPs but designed to sift out binding layer)
  -eo__, he_, only xa
*)


let sum15 o1 o2 s = 
  s  (fun x -> bind x (fun x' -> 
  o1 (fun y -> bind y (fun y' -> 
  o2 (fun z -> bind z (fun z' s -> 
    [unit (x' + y' + z' = 15) s]
  ))))));;

sum15 so so eo [];;
sum15 so (some (equals he1)) so [];;

la (lift so) (ra (ra (lift sum15) (int_lift so)) (lift (lift he1))) (fun x -> x) [];;
la (lift so) (ra (ra (lift sum15) (int_lift eo_)) (lift (lift he1))) (fun x -> x) [];;


let rel o s = 
  s (fun x -> bind x (fun x' -> 
  o (fun y -> bind y (fun y' s -> 
    [unit (x' > y' || x' < y') s]
  ))));;


rel eo so [];;
rel so eo [];;

la (int_lift so) (ra (lift rel) (lift (some (equals (succ' he))))) (fun x -> x) [];;



let sum15 o1 o2 s = 
  o1 (fun xx ->
  s  (fun x -> bind x (fun x' -> 
  (lift xx) (fun y -> bind y (fun y' -> 
  o2 (fun z -> bind z (fun z' s -> 
    [unit (x' + y' + z' = 15) s]
  )))))));;

(*to do w/NB weirdness?*)
(*tosses out subj-updated list?*)


sum15 (some thing) (lift he1) so [];;

let low' f = f (fun x -> x);;
la (lift so) (lift (low' (ra (ra (lift sum15) (lift so)) (int_lift (some (equals he)))))) (fun x -> x) [];;
la (lift so) (ra (ra (lift sum15) (lift so)) (int_lift (some (equals he1)))) (fun x -> x) [];;

(*you have to lower before meeting the binder*)
(*but lowering isn't possible in this setup till you have a prop on lower layer*)


let ll3 l r k = 
  l (fun l' ->
    r (fun r' -> 
      k (fun k' -> 
	ll l' r' k')
    ))
;;

let rr3 l r k = 
  l (fun l' ->
    r (fun r' -> 
      k (fun k' -> 
	rr l' r' k')
    ))
;;
let int_lift h c s = h (fun x s' -> c (fun k -> k x) s) s;;
