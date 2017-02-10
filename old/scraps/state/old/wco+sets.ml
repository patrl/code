let unit x = [fun s -> (x, s)];;
let unit' x = [fun s -> (x, x::s)];;

let pwfa f a = 
  List.concat 
    (List.map 
       (fun g -> (List.map g a)) f
    );;

let bind y g s =
    let (a, b) = y s in
    g a b;;

let triv = 
  [fun x -> 
    bind x (fun y s ->
      (true, s)
    )
  ];;

let equals = 
  [fun r l -> 
    bind l (fun x -> 
      bind r (fun y s ->
	(x = y, s))
    )
  ];;

let lower f = pwfa f [[]];;

let univ = [1;2;3;4;5];;

let so = 
  let drefs = fun x s -> (x, x::s) in
  List.map drefs univ;;

let he = [fun s -> (List.nth s 0, s)];;
let he1 = [fun s -> (List.nth s 1, s)];;

let forall p = 
  let rec checker list prop = match list with
    | [] -> true
    | a::b -> 
      if (prop a) = false 
      then false 
      else checker b prop in
  checker univ p;;

let rec truthy list = 
  match list with 
    | [] -> false
    | (a,b)::tail -> if a then a else
	truthy tail;;

(*negation*)
let neg p = 
  [fun s -> 
    let bool = truthy (pwfa p [s]) in
    (not bool, s)
  ];;

(*dynamic conjunction*)
let conj = 
  [fun r l -> 
    bind l (fun x -> 
      bind r (fun y s ->
	(x && y, s))
    )
  ];;

(*dynamic implication*)
let impl l r = 
  neg (pwfa (pwfa conj (neg r)) l);;

let s1 = pwfa (pwfa equals he) so;;
let s2 = pwfa (pwfa equals he) he;;

(*if a something equals itself, it equals itself*)
pwfa (impl s1 s2) [[]];;

(*univ quantification*)

let eo p = 
  [fun s ->
    let property x = 
      truthy (pwfa (pwfa p (unit' x)) [s]) in
    let bool = forall property in
    (bool, s)
  ];;

let he' p = pwfa p he;;

(*
  here's a new take on the denotation of a trace: basically the C combinator
  wonder how it'll scale up to e.g. ditransitives
*)

let c f = pwfa [fun g l r -> g r l] f;;

(*
  strong crossover - 'it equals every number'

  lower (eo (pwfa (c equals) he));;
  
  # Exception: Failure "nth".
*)

(**restricted quantification**)

let every p q = 
  [fun s ->
    let property x = 
      truthy (pwfa (impl (pwfa p (unit x)) (pwfa q (unit' x))) [s]) in
    let bool = forall property in
    (bool, s)
  ];;

let some p = 
  let drefs = fun x s -> 
    if truthy (pwfa (pwfa p (unit x)) [s]) then (x, x::s) 
      else (0, [0]) in
  List.map drefs univ
;;

lower (every (pwfa equals (unit' 2)) (pwfa equals he1));;
lower ((every triv) (pwfa equals he));;

(*
lower (every triv (pwfa (c equals) he));;
*)
