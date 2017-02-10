(***BASIC PLUMBING***)

(*pointwise functional application*)
let pwfa f a = 
  List.concat 
    (List.concat 
       (List.map 
	  (fun g -> (List.map g a)) f
       )
    );;

(*state+list "monad"*)
type state = int list;;

let unit x = [fun (s:state) -> [(x,s)]];;

let bind = 
  [fun x ->
    [fun f ->
      [fun (s:state) ->
	let app (a,y) g =
	  pwfa (g a) [y] in
	let intermed = List.map app (x s) in
	pwfa intermed [f]
      ]
    ]
  ];;

(*dynamic functional application--gives arguments binding scope over functors while putting the drefs in the functor first in the assignment.*)
let apply f a = 
  pwfa (pwfa bind a) 
    [fun x -> 
      pwfa (pwfa bind f)
	[fun g ->
	  unit (g x)
	]
    ];;

let lift_et p = 
  [fun x -> 
    apply (unit p) [x]
  ];;

let lift_eet r =
  [fun x -> 
    [fun y ->
      apply (apply (unit r) [x]) [y]
    ]
  ];;

(*lowering and existential closure*)
let rec truthy list = 
  match list with 
    | [] -> false
    | (true,s)::tail -> true
    | head::tail -> truthy tail;;

let lower f = pwfa f [[]];;

let ex_clos list =  truthy (lower list);;

(***connectives and operators***)

(*dynamic conjunction. internally and externally dynamic. passes the state as updated by s1 to s2. this is not, of course, the standard syntax for "and", but it's simple to change, and this way is better mnemonically for me.*)
let dynand s1 s2 = 
  pwfa (pwfa bind s1) 
    [fun p -> 
      pwfa (pwfa bind s2)
	[fun q ->
	  unit (p & q)
	]
    ];;

let dynand2 =
  [fun s1 ->
    [fun s2 -> 
      pwfa (pwfa bind [s1]) 
	[fun p -> 
	  pwfa (pwfa bind [s2])
	    [fun q ->
	      unit (p & q)
	    ]
	]
    ]
  ];;



(*dynamic disjunction. only externally dynamic--and then, only if each disjunct contributes a dref--need to think more about this, viz. when assignments are diff lengths*)
let dynor list1 list2 = 
  List.concat [list1; list2];;


(**test-y negation**)

(*harvesting constant-y drefs: we have a simple semantic characterization of accessibility that passes up things that don't vary in the scope of a test! the intuition: "not" collapses the innermost alternatives--only allows one (cf solomon). there's only two principled ways to do this: wipe out drefs entirely or pass up the ones that all the alternatives in the prejacent agree on. the latter seems a better fit for the data. PS: i have a suspicion this isn't the most efficient algorithm.*)
let drefs_in_common list =
  let rec get_assignments list = 
    match list with 
      | [] -> []
      | h::t -> (snd h)::(get_assignments t) in
  let rec checker list drefs n = 
    let rec is_common_at x list n = 
      match list with 
	| [] -> true
	| a::b -> 
	  if (List.nth a n) != x
	  then false 
	  else is_common_at x b n in
    if (list = [] || n = List.length (List.hd list))
    then drefs
    else 
      let a::b = list in
      let a_n = List.nth a n in
      if (is_common_at a_n list n)
      then checker list (a_n::drefs) (n+1) 
      else checker list drefs (n+1) in
  List.rev (checker (get_assignments list) [] 0);;

(*so negation does the hamblin business, but also returns the constant-y drefs in its scope---i.e. those which are the same at each of the scope's <bool,state> alternatives*)
let neg = 
  [fun p -> 
    [fun (s:state) -> 
      if truthy (p s) 
      then [(false,drefs_in_common (p s))]
      else [(true, drefs_in_common (p s))]
    ]
  ];;

(*test-y conditionals: p => q = ~(p & ~q). internally dynamic, externally static (although again constant-y drefs percolate)*)
let iffy =  
  [fun p -> 
    [fun q -> 
      pwfa neg (dynand [p] (pwfa neg [q]))
    ]
  ];;


(***checking sentences***)

(*some lexical stuff*)
let univ = [1;2;3;4;5;6;7;8;9;10];;
let j = [fun (s:state) -> [(1,1::2::s); (2,1::2::s)]];;
let m = [(fun (s:state) -> [(3,3::s)]); (fun (s:state) -> [(4,4::s)])];;
let p0 = unit (fun x -> x < 6);;
let p1 = unit (fun x -> x <= 2);;
let r0 = unit (fun x -> fun y -> x < y);;
let s0 = apply (apply r0 (List.concat [j;m])) (List.concat [j;m]);;
let s1 = apply p0 (pwfa [unit] univ);;

(*different levels for nondeterminism to live: j and j' have the same lowers (as do s3 and s4) but j will be wiped out by tests, while j' will not. in particular, here s3---roughly, "not (1 or 2 = 2)"---is false, while s4---roughly, "not (1=2) or not (2=2)" is true. so the level at which nondeterminism resides offers different scoping possibilities.*)
let j' = [(fun (s:state) -> [(1,1::2::s)]); (fun (s:state) -> [(2,1::2::s)])];;

let s3 = apply p1 j;;
let s4 = apply p1 j';;
ex_clos (pwfa neg s3);;
ex_clos (pwfa neg s4);;

(*s1 & s0*)
lower (dynand s1 s0);;

(*s1 || s0*)
lower (dynor s1 s0);;

(*no double negation elimination*)
lower s0;;
lower (pwfa neg (pwfa neg s0));;

(*we see how constants get passed up*)
lower (pwfa neg ([fun s -> [(false,1::2::3::s); (false,1::3::3::s)]]));;
lower (pwfa neg ([fun s -> [(false,1::s)]]));;
lower (pwfa (pwfa iffy s1) (pwfa neg ([fun s -> [(false,1::s)]])));;
lower (pwfa neg (pwfa neg ([fun s -> [(false,1::s)]])));;


(***pronouns***)
let he n = 
  [fun (s:state) -> 
    [
      (List.nth s n, s)
    ]
  ];;

(*e.g.*)
pwfa (he 2) [[1;2;3;4]; [5;6;7;8]];;


(***quantifiers***)

(**some: note that we end up with a GQ. this is so because bind guarantees that the functor updates the state that the argument has access to. and we want subject DPs to be able to bind into VPs. cool: if we have AR, VP could necc be a functor over subject; if we just slightly re-jigger dynfa so that arguments always update the state of functors, then we have it that we can have wide scope without WCO. on the other hand, they can outscope subject DPs!!!!! [obviously, worth double-checking]**)

let some = 
  let am_i_a_dref prop x (s:state) =
    if
      truthy (pwfa (apply [prop] (unit x)) [s]) 
    then
      pwfa
	(apply 
	   [fun (s':state) -> [((fun f -> fun p -> p x), x::s')]] 
	   [prop]
	) [s]
    else [] in
  [fun np -> 
    List.map (am_i_a_dref np) univ
  ];;


(**shifting between layers of non-determinism**)
let narrowish list = 
  [fun x ->
    pwfa list [x]
  ];;

(*compare*)
lower (pwfa neg (narrowish (apply p1 j')));;
lower (pwfa neg (apply p1 j'));;

(*problems when bound into?*)
let wideish list = 
  let lowered_list () = lower list in
  let relift (a,b) = 
    [fun (s:state) ->
      [(a, List.concat[b;s])]
    ] in
  pwfa [relift] (lowered_list ());;

(*compare*)
lower (pwfa neg (wideish (apply p1 j)));;
lower (pwfa neg (apply p1 j));;

(*in most cases, narrowing something narrow has no effect. same for wideing something wide.*)
narrowish j;;    (*length: 1, same as j*)
wideish j';;     (*length: 2, same as j'*)

(*in most cases, narrowish (wideish f) = f, and wideish (narrowish g) = g*)
narrowish (wideish j);;    (*length 1, same as j*)
wideish (narrowish j');;   (*length 2, same as j'*)

(*the exceptions to these identities occur when there are "null drefs" in the innermost layer; since applying to an s:state effectively reveals that the emperor has no clothes. those get eliminated. but these were inevitably going to be eliminated in the end anyway, so this isn't consequential.*)
wideish (pwfa some p0);;              (*length: 5; (pwfa some p0) has cardinality 10*)
wideish (narrowish (pwfa some p0));;  (*ditto*)

(**every: this way is very cool. relies on introducing the "temporary dref" at the top of the stack then feeding it to the predicate**)
let every = 
  [fun np ->
    [fun vp ->
      pwfa neg 
	(dynand 
	   (narrowish (apply (pwfa some [np]) (unit (fun y -> true)))) 
	   (pwfa neg (apply [vp] (he 0)))
	)
    ]
  ];;

let p3 = [fun s -> [((fun x -> true),3::4::s)]];;
pwfa (pwfa (pwfa every p3) p0) [[7;8]];;
pwfa (pwfa (pwfa every p0) p3) [[7;8]];;


(*q scope w/hendriks may be more straightforward if types re-arranged. but then you can't have a unitary unit, which makes giving a single application rule difficult.*)


(**another idea for indefinite binding: dividing labor between the indefinite and binding**)

(*some2 just adds an indeterminate individual to the at-issue dimension*)
let some2 = 
  let am_i_a_dref prop x (s:state) =
    if
      truthy (pwfa (apply [prop] (unit x)) [s]) 
    then
      pwfa
	(unit x) [s]
    else [] in
  [fun np -> 
    List.map (am_i_a_dref np) univ
  ];;

(*dref adds an individual to the stack*)

let rec insert_at x l i =
  if (i = 0) then x::l else
    match l with
      | [] -> x::l
      | h::t -> h::(insert_at x t (i - 1));;

let dref n = 
  [fun dp -> 
    [fun (s:state) ->
      let grab_indiv = 
	[fun (a,b) -> 
	  [(a,insert_at a b n)]
	] in
      pwfa grab_indiv (pwfa [dp] [s])
    ]
  ];;

(*useful for turning names (arbitrary constants) into binders*)
lower (pwfa (dref 0) (List.concat [(unit 2);(unit 3)]));;
lower (pwfa (dref 0) [fun s -> [(2,s);(3,s)]]);;

(*combining some2 with dref gives same result as original "some"; the latter has the identity function in there because it returned lifted individuals.*)
lower (pwfa (dref 0) (pwfa some2 p0));;
lower (apply (pwfa some p0) (unit (fun x -> x)));;

(**abstraction! this lets us do QR and scope taking**)
let lambda n = 
  [fun form ->
    [fun (s:state) -> 
      let form_length = List.length (pwfa [form] [-1::s]) in
      let rec abstract f m = 
	if m = form_length
	then [] 
	else 
	  [(
	    (fun x -> 
	      let new_s = insert_at x s n in
	      let (a,b) = List.nth (pwfa [f] [new_s]) m in
	      a
	    ),
	    s
	  )] :: abstract f (m+1) in
      List.concat (abstract form 0)
    ]
  ];;

(*testing*)
let p10 = [fun s -> [((fun x -> x = 24),s); ((fun x -> x = 25),s)]];;
pwfa (apply (unit (fun p -> p 24)) (pwfa (lambda 0) (apply p10 (he 0)))) [[]];;
lower (apply (pwfa (lambda 0) (he 0)) (unit 32));;

(**relative pronoun**)
let who rc n = 
  pwfa (pwfa bind rc) 
    [fun p -> 
      pwfa (pwfa bind n)
	[fun q ->
	  unit (fun x -> p x & q x)
	]
    ];;

(*     passes drefs in nominal to rel clause
# lower (pwfa (pwfa every (who p0 p0)) (apply r0 (he 1)));;
Exception: Failure "nth".
#  lower (pwfa (pwfa every (who p0 p3)) (apply r0 (he 1)));;
- : (bool * int list) list = [(false, [3; 4])]
*)


(*extracting functional witnesses. returning constant-y drefs an instance of this??*)

(*is BS's claim about not needing to stipulate tests right? isnt their "every" just a test? hard to see how this claim has bite without saying *how* existentials take exceptional scope*)

(*think more about layered alternatives, binding in--altho should work - connection with solomon, brasoveanu & farkas*)

(*do b&f handle exceptional binding scope too?? also they don't have a compositional language, just a first-order one ; brasoveanu anaphora to quantificational dependencies vis a vis solomon?*)

(*issues when domain of indef/univ is singleton [you create a dref corresponding to that individual], but no big deal: maxpressup/felicity/these might not be so bad anyway*)

(*binding into, out of adjuncts / inv linking || inv linking in dynamic semantics more generally*)

(*semantic characterization of WCO: which bind you choose depends on whether it's forward or backward application. NB: BS also rely on two rules for forwards/backwards combination. for them WCO is a syntactic phenomenon.*)

(*reconstruction with lambda conversion \`a la chierchia*)






lower (apply (apply (pwfa (lambda 1) (pwfa (lambda 0) (apply (apply r0 (he 0)) (he 1)))) (unit 33)) (unit 2));;

pwfa (lambda 0) (pwfa every p0);;
(*how necessary is it for "every NP" to be [fun vp -> _]? perhaps not very.*)
