(*state.list monad*) 
let unit x = fun s -> [(x,s)]
;;
let bind m f = fun s -> 
  let pair_apply f = fun (a,b) -> f a b in
  List.concat (List.map (pair_apply f) (m s))
;;

(*combination*)
let fapply f m = 
  bind f (fun g -> bind m (fun x -> unit (g x)))
;;
let bapply m f = 
  bind m (fun x -> bind f (fun g -> unit (g x)))
;;

(*lexicon*)
let univ = [1;2;3;4;5;6;7;8;9;10]
;;

(**logical bits**)

let conj = unit (fun p q -> p & q)
;;
let some p = fun s ->
  let rec replace list x = 
    match list with 
      | [] -> []
      | (bool,s)::b ->
	if bool then (x, x::s)::(replace b x) else replace b x in
  let pairs x = bind (unit x) (fun y -> 
      bind p (fun q -> unit (q y))) s in
  let hybrid x = replace (pairs x) x in
  List.concat (List.map hybrid univ)
;;
let rec truthy list = 
  match list with 
    | [] -> false
    | (true,s)::b -> true
    | a::b -> truthy 
b;;

let collapse list =
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
  List.rev (checker (get_assignments list) [] 0)
;;

let neg p = fun s -> [(not (truthy (p s)), collapse (p s))]
;;

(**predicates**)
let p1 = unit (fun x -> x <= 5);;
let p2 = unit (fun x -> x >= 5);;
let p3 = unit (fun x -> x = 3);;
let r1 = unit (fun x y -> x = y);;
let r2 = unit (fun x y -> x > y);;

let he n = fun s -> [(List.nth s n, s)];;

(*tests*)

(**indefiniteness interacts**)
bapply
  (some p1)
  (fapply
     r1
     (some p1)
  )
  []
;;

(**[strong] donkey anaphora out of DP**)
let every p q = 
  neg 
    (bind 
       (some p) 
       (fun x ->
	 neg 
	   (bind 
	      q
	      (fun q' -> unit (q' x))
	   )
       )
    )
;;

every 
  (fapply r2 (some p1))
  (fapply r2 (he 1)) 
  []
;;


(*constants percolate; tested with singleton indefinites*)
(**clausal negation**)
neg 
  (bapply 
     (some 
	(fapply 
	   r1 
	   (unit 3)
	)
     )
     (fapply
	r1
	(some p2)
     )
  )  
 []
;;

(**partially dynamic determiners*)
every 
  (fapply r2 (some (fapply r1 (unit 3))))
  (fapply r2 (he 1)) 
  []
;;

(**exceptional scope**)
bind 
  (bapply 
     (some p1) 
     p2
  ) 
  (fun p -> neg (unit p))
  []
;;

bind 
  (fapply 
     r1 
     (some p1)
  )
  (fun p -> every
    (unit p) 
    (fapply
       r1 
       (unit 3)
    )
  ) []
;;

let p4 = 
  let p = fun x -> x = 3 in
  fun s -> [(p, p::s)]
;;

bapply 
  (bapply (some p1) p4) 
  (fapply 
     conj
     (bapply (some p2) (he 0))
  )
  []
;;
