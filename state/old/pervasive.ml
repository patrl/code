let pwfa f a = 
  List.concat 
    (List.concat 
       (List.map (fun g -> (List.map g a)) f)
    );;

let and1 = [fun p -> [fun q -> [p & q]]];;

let lift_et f = 
  [fun x -> 
    [fun i -> 
      [fun k -> 
	pwfa (pwfa and1 [f x]) (k i)
      ]
    ]
  ];;

let lift_eet f = 
  [fun x -> 
    [fun y -> 
      [fun i -> 
	[fun k -> 
	  pwfa (pwfa and1 [f x y]) (k i)
	]
      ]
    ]
  ];;

let rec print_list list = 
  match list with 
      [] -> print_string ""
    | a::b -> (fun () -> print_list b) (print_int a);;

let i0 = [[]];;
let k0 = 
  [fun i -> 
    [(fun () -> true) (print_list i)]
  ];;
let lower prop = pwfa (pwfa prop i0) k0;;

let p1 x = x < 3;;
let r1 x y = x <= y;; 
let univ = [1;2;3;4;5];;

(*testing a simple sentence: "a number [1,5] < 3"*)
let p1_up = lift_et p1;;
let s = pwfa p1_up univ in
lower s;;

(*another: "a number [1,5] <= a number [1,5]"*)
let r1_up = lift_eet r1 in 
let vp = pwfa r1_up univ in
let s = pwfa vp univ in 
lower s;;

(*one with drefs: "john(1) or mary(5) < 3". notice the printed output.*)

let john = 
  [fun p -> 
    [fun i ->
      [fun k -> 
	pwfa (pwfa (p 1) [1::i]) [k]
      ]
    ]
  ];;

let mary = 
  [fun p -> 
    [fun i ->
      [fun k -> 
	pwfa (pwfa (p 5) [5::i]) [k]
      ]
    ]
  ];;

let dp = List.concat[john; mary] in 
let s = pwfa dp (lift_et p1) in 
lower s;;

let exists p = 
  let rec check list = match list with 
      [] -> false
    | a::b -> 
      if (a = true) 
      then true 
      else check b in
  check (pwfa p univ);;

let some = 
  [fun p -> 
    [fun q ->
      [fun i ->
	[fun k -> 
	  [exists
	    [fun x ->
	      pwfa (pwfa (p x) [i])
		[fun i' -> pwfa (pwfa (q x) [i']) [k]]
	    ]
	  ]
	]
      ]
    ]
  ];; 

(*testing*)
let p0 = fun x -> false;;
let p0_up = lift_et p0;;
lower (pwfa (pwfa some (lift_et p1)) (lift_et p0));;
lower (pwfa (pwfa some (lift_et p1)) (lift_et p1));;


(*alternatives percolate around "some"? "every"? currently "every" just wipes them out.
matter of "every" taking scoping over the monad or not.*)

(*pointwise "or"*)
let or_ = 
  [fun p -> 
    [fun q -> 
      [fun i -> 
	[fun k -> 
	  List.concat [pwfa (p i) [k]; pwfa (q i) [k]]
	]
      ]
    ]
  ];;

(*hamblin "or"*)
let or2 a b = List.concat[a;b];;

(*pointwise "and"*)
let and_ = 
  [fun p -> 
    [fun q -> 
      [fun i -> 
	[fun k -> 
	  pwfa (p i) [fun j -> pwfa (q j) [k]]
	]
      ]
    ]
  ];;

let rec truths list = match list with 
    [] -> [] 
  | true::tail -> true::(truths tail)
  | head::tail -> truths tail;;

(*test-y "not"*)
let not_ s = 
  [fun i ->
    [fun k -> 
      if
	truths (pwfa (pwfa s [i]) [fun j -> [true]]) = [] 
      then 
	pwfa [k] [i] 
      else 
	[false]
    ]
  ];;

(*test-y "if"*)
let if_ p q = 
  not_ (pwfa (pwfa and_ p) (not_ q));;

let forall p = 
  let rec check list = match list with 
      [] -> true
    | a::b -> 
      if (a = false) 
      then false 
      else check b in
  check (pwfa p univ);;

(*test-y "every"*)
let every_ p q = 
  [fun i ->
    [fun k -> 
      [forall 
	[fun x ->
	  pwfa (pwfa (if_ (pwfa p [x]) (pwfa q [x])) [i]) [k]
	]
      ]
    ]
  ];;
      

let s1 = (pwfa p1_up univ);;
let s2 = (pwfa p0_up univ);;
lower (pwfa (pwfa and_ s1) s1);;
lower (pwfa (pwfa or_ s1) s1);;
lower (pwfa (pwfa and_ s1) s2);;
lower (pwfa (pwfa or_ s1) s2);;

(*todo: functional witnesses, percolating alternatives past tests w/o lexical ambiguity*)

(*pronouns*)
let he n = 
  [fun p -> 
    [fun i -> 
      [fun k -> 
      pwfa (pwfa (p (List.nth i n)) [i]) [k]
      ]
    ]
  ];;

(*testing a simple binding example: "john left. he left."*)
let s1 = pwfa john (lift_et p1) in
let s2 = pwfa (he 0) (lift_et p1) in
lower (pwfa (pwfa and_ s1) s2);;

(*mary left. she left.*)
let s1 = pwfa mary (lift_et p1) in
let s2 = pwfa (he 0) (lift_et p1) in
lower (pwfa (pwfa and_ s1) s2);;

(*john or mary left. s/he left.*)
let dp = List.concat[john; mary] in 
let s1 = pwfa dp (lift_et p1) in 
let s2 = pwfa (he 0) (lift_et p1) in
lower (pwfa (pwfa and_ s1) s2);;

(*donkey binding. if john left, he left*)
let s1 = pwfa john (lift_et p1) in
let s2 = pwfa (he 0) (lift_et p1) in
lower (if_ s1 s2);;

(*test-y-ness leads to presupp failure outside test's scope*)
let s1 = pwfa mary (lift_et p1) in
let s2 = not_ (pwfa (he 0) (lift_et p1)) in
lower (pwfa (pwfa and_ (if_ s1 s2)) s2);;

(*disjunctive binding: "if john/mary left, s/he left."*)
let dp = List.concat[john;mary] in
let s1 = pwfa dp (lift_et p1) in
let s2 = pwfa (he 0) (lift_et p1) in
lower (if_ s1 s2);;

(*hamblin "some"*)
let some_ p = 
  let rec true_list list = 
    match list with 
	[] -> false
      | true::b -> true
      | a::b -> true_list b in 
  let alt = 
    [fun x ->
      [fun p -> 
	[fun q -> 
	  [fun i ->
	    [fun k ->
	      if 
		true_list (pwfa (pwfa (p x) [i]) [fun j -> [true]])
	      then 
		pwfa 
		  (pwfa (p x) [i])
		  [fun j -> pwfa (pwfa (q x) [x::j]) [k]]
	      else 
		[]
	    ]
	  ]
	]
      ]
    ] in
  pwfa (pwfa alt univ) p;;

(*testing: "some n<3 <3"*)
lower (pwfa (some_ (lift_et p1)) (lift_et p1));;

(*testing: "some n!=n <3"*)
lower (pwfa (some_ (lift_et p0)) (lift_et p1));;

(*rel pronoun*)
let who_ = 
  [fun p -> 
    [fun q ->
      [fun x ->
	[fun i ->
	  [fun k ->
	    pwfa 
	      (pwfa (p x) [i])
	      [fun j -> pwfa (pwfa (q x) [j]) [k]]
	  ]
	]
      ]
    ]   
  ];;

(*testing: some n<3 which is <3 is <3*)
lower (pwfa (some_ (pwfa (pwfa who_ (lift_et p1)) (lift_et p1))) (lift_et p1));;

(*every n>=1 which is <3 is non-self-equal*)
lower (every_ (pwfa (pwfa who_ (pwfa (lift_eet r1) [1])) (lift_et p1)) (lift_et p0));;


(*fucking with the layer the nondeterminism lives in allows you to control whether alternatives percolate past/are bound by an operator!!*)

(*hamblin "some", second try*)
let some_2 = 
  let rec true_list list = 
    match list with 
	[] -> false
      | true::b -> true
      | a::b -> true_list b in 
  let alt p q i k x =
    if 
      true_list (pwfa (pwfa (p x) [i]) [fun i -> [true]])
    then 
      pwfa 
	(pwfa (p x) [i])
	[fun j -> pwfa (pwfa (q x) [x::j]) [k]]
    else 
      [] in
  [fun p ->
    [fun q ->
      [fun i ->
	[fun k ->
	  List.concat (List.map (alt p q i k) univ)
	]
      ]
    ]
  ];;

(*testing: some n<3 <3*)
lower (pwfa (pwfa some_2 (lift_et p1)) (lift_et p1));;

(*some n>1 <3*)
lower (pwfa (pwfa some_2 (lift_et (fun x -> x > 1))) (lift_et p1));;

(*some n<3 which is <3 is <3*)
lower (pwfa (pwfa some_2 (pwfa (pwfa who_ (lift_et p1)) (lift_et p1))) (lift_et p1));;

let ar = 
  [fun r ->
    [fun q ->
      [fun y ->
	[fun i ->
	  [fun k ->
	    pwfa (pwfa (q (fun x -> pwfa (r x) [y])) [i]) [k]
	  ]
	]
      ]
    ]
  ];;

(*testing: 1>=mary(5)*)
lower (pwfa (pwfa (pwfa ar (lift_eet r1)) mary) [1]);;

(*testing: 1 >= some n < 3*)
lower (pwfa (pwfa (pwfa ar (lift_eet r1)) (pwfa some_2 (lift_et p1))) [1]);;

(*full-fledged BOODP example: every n<3 >= some m<3 >= it, using both entries for "some"*)
lower (every_ (pwfa (pwfa who_ (pwfa (pwfa ar (lift_eet r1)) (pwfa some_2 (lift_et p1)))) (lift_et p1)) (pwfa (pwfa ar (lift_eet r1)) (he 0)));;

lower (every_ (pwfa (pwfa who_ (pwfa (pwfa ar (lift_eet r1)) (some_ (lift_et p1)))) (lift_et p1)) (pwfa (pwfa ar (lift_eet r1)) (he 0)));;

(*lets us redefine "every" pointwised-ly*)

(*test-y "every"*)
let every_2 =
  [fun p ->
    [fun q ->
      [fun i ->
	[fun k -> 
	  [forall 
	      [fun x ->
		pwfa (pwfa (if_ (p x) (q x)) [i]) [k]
	      ]
	  ]
	]
      ]
    ]
  ];;

(*now we can see how the place where the nondeterminism lives has an effect on just how test-y something is*)
lower (pwfa (pwfa every_2 (pwfa (pwfa who_ (pwfa (pwfa ar (lift_eet r1)) (some_ (lift_et p1)))) (lift_et p1))) (pwfa (pwfa ar (lift_eet r1)) (he 0)));;

lower (pwfa (pwfa every_2 (pwfa (pwfa who_ (pwfa (pwfa ar (lift_eet r1)) (pwfa some_2 (lift_et p1)))) (lift_et p1))) (pwfa (pwfa ar (lift_eet r1)) (he 0)));;

(*problem: wipes out binding*)
(*interesting: poss gives way to get handle on specificity vis a vis accessibility?*)
(*tests have something to do with **collapsing** innermost alternatives*)
(*if List.length = 1 then k i'; if >1, just give k i*)

(*reformulating negation*)
let neg_2 = 
  [fun s ->
    [fun i ->
      [fun k ->
	let downstairs = (pwfa (s i) [fun j -> [true]]) in
	let harvest_i f = fun i -> [] in 
	if
	  truths downstairs = [] 
	then 
	  if
	    List.length downstairs = 1
	  then
	    pwfa [k] [i]
	  else
	    pwfa [k] [i] 
	else 
	  [false] (*why not []?*)
      ]
    ]
  ];;

