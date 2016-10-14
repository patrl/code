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

(*dynamic functional application--gives arguments binding scope over functors while putting the drefs in the functor first in the assignment -- i.e. semantics of leftward application*)
let apply f a = 
  pwfa (pwfa bind a) 
    [fun x -> 
      pwfa (pwfa bind f)
	[fun g ->
	  unit (g x)
	]
    ];;

(*gives functors binding scope over arguments -- i.e. semantics of rightward application*)
let apply2 f a = 
  pwfa (pwfa bind f) 
    [fun g -> 
      pwfa (pwfa bind a)
	[fun x ->
	  unit (g x)
	]
    ];;

let lift_et p = 
  [fun x -> 
    apply (unit p) [x]
  ];;

(*mucking w/apply/apply2 changes dref order in assignments*)
let lift_eet r =
  [fun x -> 
    [fun y ->
      apply (apply2 (unit r) [x]) [y]
    ]
  ];;

(*lowering and existential closure*)

let rec truths list = 
  match list with 
    | [] -> []
    | (true,s)::tail -> (true,s)::(truths tail)
    | head::tail -> truths tail;;

let rec truthy list = truths list != [];;

let lower f = pwfa f [[]];;

let ex_clos list =  truthy (lower list);;

(***connectives and operators***)

(*dynamic conjunction. internally and externally dynamic. passes the state as updated by s1 to s2. this is not, of course, the standard syntax for "and" (this one combines with the leftmore conjunct first) but it's simple to change, and this way is better mnemonically for me.*)
let dynand =
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
  let rec min_length l = 
    match l with 
      | [] -> 0
      | a::[] -> List.length a
      | a::b ->
	min (List.length a) (min_length b) in
  let rec checker list drefs n = 
    let rec is_common_at x list n = 
      match list with 
	| [] -> true
	| a::b -> 
	  if (List.nth a n) != x
	  then false 
	  else is_common_at x b n in
    if (list = [] || n = min_length list)
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
      if p s = [] then [] else
	let bool = truthy (p s) in
	[(not bool,drefs_in_common (p s))]
    ]
  ];;

let neg_test = 
  [fun p -> 
    [fun (s:state) -> 
      if p s = [] then [] else
	let bool = truthy (p s) in
	[(not bool,s)]
    ]
  ];;


(*test-y conditionals: p => q = ~(p & ~q). internally dynamic, externally static (although again constant-y drefs percolate)*)
let iffy =  
  [fun p -> 
    [fun q -> 
      pwfa neg (pwfa (pwfa dynand [p]) (pwfa neg [q]))
    ]
  ];;



(***checking sentences***)

(*some lexical stuff*)
let univ = [1;2;3;4;5;6;7;8;9;10];;
let j = [fun (s:state) -> [(1,1::2::s); (2,1::2::s)]];;
let j' = [(fun (s:state) -> [(1,1::2::s)]); (fun (s:state) -> [(2,1::2::s)])];;
let m = [(fun (s:state) -> [(3,3::s)]); (fun (s:state) -> [(4,4::s)])];;
let p0 = lift_et (fun x -> x < 6);;
let p1 = lift_et (fun x -> x <= 2);;
let r0 = lift_eet (fun x -> fun y -> x < y);;
let r1 = lift_eet (fun x -> fun y -> x = y);;
let s0 = pwfa (pwfa r0 (List.concat [j;m])) (List.concat [j;m]);;
let s1 = pwfa p0 (pwfa [unit] univ);;

(*different levels for nondeterminism to live: j and j' have the same lowers (as do s3 and s4) but j' takes wide scope.*)


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

(*dynamic binding: "some"*)

let rec replace_fst x list = 
  match list with 
    | [] -> []
    | (a,b)::tail -> (x,b)::(replace_fst x tail);;

let some = 
  let am_i_a_dref prop x (s:state) =
    if
      truthy (pwfa (pwfa [prop] (unit x)) [s]) 
    then
      pwfa
	(pwfa
	   [fun prop' ->
	     [fun s -> 
	       replace_fst x (truths (prop' s))
	     ]
	   ]
	   (pwfa [prop] (unit x))) 
	[List.concat [s;[x]]]
    else [] in
  [fun np -> 
    [fun s -> 
      pwfa (List.map (am_i_a_dref np) univ) [s]
    ]
  ];;



(**another idea for indefinite binding: dividing labor between the indefinite and binding**)

(*some2 just adds an indeterminate individual to the at-issue dimension*)
let some2 = 
  let am_i_a_dref prop x (s:state) =
    if
      truthy (pwfa (pwfa [prop] (unit x)) [s]) 
    then
      pwfa
	(pwfa
	   [fun prop' ->
	     [fun s -> 
	       replace_fst x (truths (prop' s))
	     ]
	   ]
	   (pwfa [prop] (unit x))) 
	[s]
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

(*combining some2 with dref gives same result as original "some".*)
lower (pwfa (dref 0) (pwfa some2 p0));;
lower (pwfa some p0);;


(**shifting between layers of non-determinism**)
let narrowish list = 
  [fun x ->
    pwfa list [x]
  ];;

(*compare*)
lower (pwfa neg (narrowish (pwfa p1 j')));;
lower (pwfa neg (pwfa p1 j'));;

(*problems when bound into?*)
let wideish list = 
  let lowered_list () = lower list in
  let relift (a,b) = 
    [fun (s:state) ->
      [(a, List.concat[b;s])]
    ] in
  pwfa [relift] (lowered_list ());;

(*compare*)
lower (pwfa neg (wideish (pwfa p1 j)));;
lower (pwfa neg (pwfa p1 j));;

(*in most cases, narrowing something narrow has no effect. same for wideing something wide.*)
narrowish j;;    (*length: 1, same as j*)
wideish j';;     (*length: 2, same as j'*)

(*in most cases, narrowish (wideish f) = f, and wideish (narrowish g) = g*)
narrowish (wideish j);;    (*length 1, same as j*)
wideish (narrowish j');;   (*length 2, same as j'*)

(*the exceptions to these identities occur when there are "null drefs" in the innermost layer; since applying to an s:state effectively reveals that the emperor has no clothes. those get eliminated. but these were inevitably going to be eliminated in the end anyway, so this isn't consequential.*)
wideish (pwfa some p0);;              (*length: 5; (pwfa some p0) has cardinality 10*)
wideish (narrowish (pwfa some p0));;  (*ditto*)

(**every: relies on introducing the "temporary dref" at the top of the stack then feeding it to the predicate**)
(*need to fix indexing; formerly had he_1 - why?*)

let every = 
  [fun np ->
    [fun vp ->
      [fun s ->
	let property = fun x ->
	  pwfa
	    (pwfa neg 
	       (pwfa
		  (pwfa dynand 
		     (narrowish (pwfa 
			[np] 
			(pwfa (dref 0) (unit x))))
		  )
		  (pwfa neg 
		     (narrowish (pwfa 
			[vp] 
			(unit x)))
		  )
	       )
	    ) [s] in
	let new_list = 
	  List.concat (List.map property univ) in
	let all_truths list = 
	  truths list = list in
	if new_list = [] then [] else
	  if all_truths new_list  (*true in case of vacuous quantification?*)
	  then [(true,  drefs_in_common new_list)]
	  else [(false, drefs_in_common new_list)]
      ]
    ]
  ];;
   
let p3 = 
  [fun x -> 
    let guts = [fun s -> [((fun x -> true),3::4::s);((fun x -> true),1::2::s)]] in
    apply guts [x]
  ];;

pwfa (pwfa (pwfa every p3) p0) [[7;8]];;
pwfa (pwfa (pwfa every p0) p3) [[7;8]];;




(*extracting functional witnesses. returning constant-y drefs an instance of this??*)

(*is BS's claim about not needing to stipulate tests right? isnt their "every" just a test? hard to see how this claim has bite without saying *how* existentials take exceptional scope*)

(*think more about layered alternatives, binding in--altho should work - connection with solomon, brasoveanu & farkas*)

(*do BF handle exceptional binding scope too?? also they don't have a compositional language, just a first-order one ; brasoveanu anaphora to quantificational dependencies vis a vis solomon?*)

(*issues when domain of indef/univ is singleton [you create a dref corresponding to that individual], but no big deal: maxpressup/felicity/these might not be so bad anyway*)

(*binding into, out of adjuncts / inv linking || inv linking in dynamic semantics more generally*)

(*semantic characterization of WCO: which bind you choose depends on whether it's forward or backward application. NB: BS also rely on two rules for forwards/backwards combination. for them WCO is a syntactic phenomenon.*)

(*reconstruction with lambda conversion \`a la chierchia*)




(*quantifier scope*)
let sws verb = 
  [fun q ->
    [fun dp ->
      pwfa [q]
	[fun dp' -> 
	  pwfa (pwfa verb [dp']) [dp]
	]
    ]
  ]

let ows verb = 
  [fun q1 ->
    [fun q2 ->
      pwfa [q1]
	[fun dp1 ->
	  pwfa [q2] 
	    [fun dp2 -> 
	      pwfa (pwfa verb [dp1]) [dp2]
	    ]
	]
    ]
  ]

let ar = (*cf. T*)
  [fun f ->
    [fun q -> 
      q f
    ]
  ]

let comp = (*cf. B*)
  [fun a ->
    [fun b ->
      [fun c ->
	pwfa [a] (b c)
      ]
    ]
  ];;

let ar_in = 
  [fun verb -> 
    pwfa (pwfa comp ar) [verb]
  ];;

let ar_out  = 
  [fun verb -> 
    [fun q ->
      [fun dp ->
	pwfa [q]
	  [fun dp' -> 
	    pwfa (verb dp') [dp]
	  ]
      ]
    ]
  ];;

let surface_scope verb = pwfa ar_in (pwfa ar_out verb);;
let inverse_scope verb = pwfa ar_out (pwfa ar_in verb);;


(*note: things are added at wrong place - index doesn't stay constant*)
let lambda n =
  [fun qp ->
    [fun dp ->
      [fun vp -> 
	let update_state =
	  apply2
	    (unit (fun x y -> y)) 
	    (pwfa (dref n) [dp]) in
	apply2
	  update_state 
	  (qp vp)
      ]
    ]
  ];;

lower (pwfa (pwfa (pwfa (lambda 3) (pwfa every p0)) (unit 0)) (pwfa r0 (he 1)));;

(*can we get away with no lambda abstraction? just direct binding?*)

(*note that this duplicates alternatives and drefs. annoying, but harmless since x is never filled by an actual dref/alternative-harboring thing*)
let who =
[fun rc ->
  [fun n ->
    [fun x ->
      apply (apply (unit (fun p q -> p & q)) (rc x)) (n x)
    ]  
  ]
];;

let dynand2 =
[fun s1 ->
  [fun s2 ->
    apply2 (apply2 (unit (fun p q -> p & q)) [s1]) [s2]  
  ]
];;

(*need to think about this*)
(*every m > n is s.t. m > n*)
(*problem for dynamics? | how does it work?/in hamblin versions?*)

(*same, just diff order*)
lower (pwfa some (pwfa (pwfa who (pwfa r0 (pwfa some p0))) p0));;
lower (pwfa some (narrowish (pwfa (pwfa who (pwfa r0 (pwfa some p0))) p0)));;

(*have a look; need to fix indexing ; current way is in tension with inverse linking*)
lower (pwfa (pwfa every (narrowish (pwfa (pwfa who (pwfa r1 (pwfa some p0))) p0))) (pwfa r1 (he 0)));;
lower (pwfa (pwfa every (pwfa (pwfa who (pwfa r1 (narrowish (pwfa some p0)))) p0)) (pwfa r1 (he 0)));;



(*using dref + some2*)
lower (pwfa (dref 1) (pwfa some2 (pwfa (pwfa who (pwfa r0 (pwfa some p0))) p0)));;
lower (pwfa (dref 1) (pwfa some2 (narrowish (pwfa (pwfa who (pwfa r0 (pwfa some p0))) p0))));;

(*crossover not avoided [should/would throw exception error]*)
lower (pwfa (pwfa (pwfa ar_out r1) (pwfa every p0)) (he 0));;

(*inv linking (why 3 drefs?)*)
let r3 = fun x y -> true;;
let r2 = lift_eet r3;;
lower (pwfa (pwfa (pwfa ar_out (pwfa (lambda 0) (pwfa every (pwfa r2 (he 0))))) (pwfa every p0)) (pwfa r0 (he 0)));;
(*cf. lower (pwfa (pwfa r1 (he 0)) (pwfa some2 (pwfa (pwfa ar_out r0) (pwfa every p0))));;*)



let member = fun x s -> [(x,List.concat[s;[x]])];;
let won = [member 1; member 2; member 5; member 6];;
let too = [member 3; member 8];;

(*4 possibilities for scope*)
(pwfa (pwfa r0 (narrowish won)) (narrowish too));;
(pwfa (pwfa r0 (narrowish won)) (too));;
(pwfa (pwfa r0 (won)) (narrowish too));;
(pwfa (pwfa r0 (won)) (too));;

(*all have same lowers, modulo order of elements*)
lower (pwfa (pwfa r0 (narrowish won)) (narrowish too));;
lower (pwfa (pwfa r0 (narrowish won)) (too));;
lower (pwfa (pwfa r0 (won)) (narrowish too));;
lower (pwfa (pwfa r0 (won)) (too));;

(*but interact with tests differently; only drefs which percolate are the non-narrowed ones.  no need for polyadic quantification/ambiguity. NB: #4 is true.*)
lower (pwfa neg (pwfa (pwfa r0 (narrowish won)) (narrowish too)));;
lower (pwfa neg (pwfa (pwfa r0 (narrowish won)) (too)));;
lower (pwfa neg (pwfa (pwfa r0 (won)) (narrowish too)));;
lower (pwfa neg (pwfa (pwfa r0 (won)) (too)));;

(*when restrictor is empty, inevitably end up with []*)
lower (pwfa p0 (pwfa some (lift_et (fun x -> false))));;

lower (pwfa (pwfa every p0) (pwfa r1 (narrowish (pwfa some (pwfa r1 (he 0))))));; 
lower (pwfa (pwfa every p0) (pwfa r1 (pwfa some (pwfa r1 (he 0)))));; 

lower (pwfa (pwfa r1 (pwfa some (pwfa r1 (he 0)))) (pwfa some p0));; 
lower (pwfa (pwfa r1 (pwfa some (pwfa r0 (he 0)))) (pwfa some p0));; 
lower (pwfa (pwfa r0 (pwfa some (pwfa r1 (he 0)))) (pwfa some p0));; 
lower (pwfa (pwfa r0 (pwfa some (pwfa r0 (he 0)))) (pwfa some p0));; 

(*apply2 in lift_eet was fucking things up??*)

(*think about wide scope restrictor, interaction with wide nuc scope indefs*)

let every2 = 
  [fun np ->
    [fun vp ->
      pwfa neg 
	(pwfa (pwfa dynand 
	   (narrowish (pwfa (lift_et (fun y -> true)) (pwfa some [np]))))
	   (pwfa neg (pwfa [vp] (he 0)))
	)
    ]
  ];;


let ok = 
  [fun np ->
    [fun vp ->
      [fun s ->
	let property x =
	  (pwfa  
	     (pwfa 
		(pwfa iffy 
		   (pwfa [np] (unit x)))
		[fun s -> pwfa (pwfa [vp] (unit x)) [x::s]]))
	     [s] in 
	let applied = pwfa [property] univ in
	let rec all_truths list = 
	  match list with 
	    | [] -> true
	    | pair::tail -> 
	      if (fst pair) = false 
	      then (fst pair)
	      else all_truths tail in
	if applied = [] then [] else 
	  if all_truths applied 
	  then [(true, drefs_in_common applied)]
	  else [(false,drefs_in_common applied)]
      ]
    ]
  ];;


let r4 = lift_eet (fun x y -> x <= y);;
let r5 = lift_eet (fun x y -> x >= y);;
lower (pwfa (pwfa every p0) (pwfa r1 (pwfa some (pwfa r4 (he 0)))));; 
lower (pwfa (pwfa every2 p0) (pwfa r1 (pwfa some (pwfa r4 (he 0)))));; 
lower (pwfa (pwfa ok p0) (pwfa r1 ((pwfa some (pwfa r4 (he 0))))));; 

(*
(*every number = every number = it | true*)
lower (pwfa (pwfa ok p0) (pwfa (pwfa ar_out r1) (pwfa ok (pwfa r1 (he 0)))));;
(*every number = every number >=  it | false*)
lower (pwfa (pwfa ok p0) (pwfa (pwfa ar_out r1) (pwfa ok (pwfa r4 (he 0)))));;
(*every number >= every number = it | true*)
lower (pwfa (pwfa ok p0) (pwfa (pwfa ar_out r4) (pwfa ok (pwfa r1 (he 0)))));;

(*every number = every number = it | true*)
lower (pwfa (pwfa (surface_scope r1) (pwfa ok (pwfa r1 (he 0)))) (pwfa ok p0));;
(*every number = every number >=  it | false*)
lower (pwfa (pwfa (surface_scope r1) (pwfa ok (pwfa r4 (he 0)))) (pwfa ok p0));;
(*every number >= every number = it | true*)
lower (pwfa (pwfa (surface_scope r4) (pwfa ok (pwfa r1 (he 0)))) (pwfa ok p0));;
*)

