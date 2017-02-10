type e = int
type t = bool
type s = int list
type 'a k = 'a -> s -> (t * s) list
type 'a monad = 'a k -> s -> (t * s) list
;;

let unit (a: 'a) : 'a monad = fun k -> k a
;;
let bind (a: 'a monad) (f: 'a -> 'b monad) : 'b monad = 
  fun k -> a (fun x -> f x k)
;;

let lapply (m: 'a monad) (h: ('a -> 'b) monad) : 'b monad = 
  bind m 
    (fun x -> bind h 
      (fun f -> unit (f x))
    )
;;
let rapply (h: ('a -> 'b) monad) (m: 'a monad) : 'b monad = 
  bind h 
    (fun f -> bind m 
      (fun x -> unit (f x))
    )
;;

let lower (f: t monad) : (t * s) list =
  f (fun x s -> [(x,s)]) []     (*the continuation here is state.list's unit!*)
;;

let univ : e list = [1;2;3;4;5;6;7;8;9;10];;
let one : e monad = fun k s -> k 1 (s@[1]);;
let he n : e monad = fun k s -> k (List.nth s n) s;;

let leq3 : (e -> t) monad =
  unit (fun x -> x <= 3)
;;
let eq : (e -> e -> t) monad = 
  unit (fun x y -> x = y)
;;
let lt : (e -> e -> t) monad =
  unit (fun x y -> y < x)
;;
let triv : (e -> t) monad = 
  unit (fun x -> true)
;;

(*1 <= 3*)
let x = lapply one leq3 in
lower x
;;


(**quantification using choice functions**)

(*first, enumerate all the [necessary] choice functions*)
(*cfs get harmlessly repeated when |univ| > |p|*)
let cfs ls =
  let rec p_to_list p ls = 
    match ls with 
      | [] -> []
      | a::b -> 
	if p a 
	then a::(p_to_list p b)
	else p_to_list p b in
  let length = List.length ls in
  let cf_n = fun n p -> 
    let p_list = p_to_list p univ in
    if n >= List.length p_list 
    then List.nth p_list (List.length p_list - 1)
    else List.nth p_list n in
  let rec add_cf n = 
    if n = length
    then []
    else (cf_n n)::(add_cf (n+1)) in
  add_cf 0
;;

(*some*)
let some : ((e -> t) -> e) monad = 
  fun k s ->
    List.concat 
      (List.map 
	 (fun f -> k f s)
	 (cfs univ)
      )
;;

(*giving stuff an anaphoric charge -- could be polymorphic with a more flex stack*)
let up (m: e monad) : e monad = fun k -> 
  m (fun x s -> k x (s@[x]))
;;

(*some x<=3 equals itself*)
let x = 
  lapply 
    (up (rapply some leq3)) 
    (rapply
       eq
       (he 0)
    ) in
lower x
;;

(*every*)

(*stack flattening : there must be a better way!*)
let compress pairs =
  let rec c l r = match (l, r) with
    | (h::t, h'::t') -> (if h==h' then h else -1) :: c t t'
    | _ -> []
  in
    match List.map snd pairs with
      | h::t -> List.filter ((<) 0) (List.fold_left c h t)
      | _ -> []
;;


let every : ((e -> t) -> e) monad = 
  fun k s ->
    let ls = some k s in
    [(List.for_all (fun (a,b) -> a) ls, compress ls)]
;;

(*every x<=3 equals itself*)
let x = 
  lapply 
    (up (rapply every leq3)) 
    (rapply
       eq
       (he 0)
    ) in
lower x
;;

(*deterministic drefs percolate*)
let x = 
  lapply 
    (up (rapply every leq3)) 
    (rapply
       eq
       (up (rapply some (rapply eq (unit 3))))
    ) in
lower x
;;

(*donkey binding out of DP*)
(*every x equal to some y<=3 equals it*)
let x = 
  lapply 
    (up (rapply every (rapply eq (up (rapply some leq3))))) 
    (rapply
       eq
       (he 1)               (*he 0 would grab the subject*)
    ) in
lower x
;;

(*binding into DP*)
(*every x<=3 equals something equal to it*)
let x = 
  lapply 
    (up (rapply every leq3)) 
    (rapply
       eq
       (rapply some (rapply eq (he 0)))
    ) in
lower x
;;

(**cross-sentential anaphora**)
(*special bind and application for indefiniteness*)
let dyn_bind (a: 'a monad) (f: 'a -> 'b monad) : 'b monad = 
  fun k s -> 
    let lowered = (a (fun x s -> [(x,s)]) s) in
    List.concat (List.map (fun (a,b) -> f a k b) lowered)
;;

let sentence_apply (a: t monad) (h: (t -> t) monad) : t monad = 
  dyn_bind a 
    (fun p -> bind h 
      (fun f -> unit (f p))
    )
;;

(*some x<=3 <= 3 ; it's <= 3*)
(*NB: substituting every for some correctly throws an exception*)
let x = 
  sentence_apply
    (lapply
       (up (rapply some leq3))
       leq3
    )
    (rapply
       (unit (&))
       (lapply (he 0) leq3)
    ) in
lower x
;;

(*note that dyn_bind gives indefiniteness scope over the continuation but not universalness. so if dyn_bind and bind are both available, this predicts, correctly, that indefinites can take 'exceptional scope' alongside 'normal scope'--of both the quantificational and binding varieties--while universals cannot ; but need to think more about the implications of this [still need theory of islands, etc]*)

(*dyn_bind only applies to propositions*)

(*crossover, reconstruction*)

(*think more about stacks of unequal lengths*)

(*RNR*)

(*

  some exception errors -- quantifiers presuppose nonemptiness of their domain -- when this presupposition is bound into, it projects universally (heim 1983).

let x =
  lapply
    (up (unit 10))
    (rapply eq
       (up (rapply 
	  some 
	  (rapply eq (he 0))
	))
    ) in
lower x
;;

let x = 
  lapply
    (rapply 
       some 
       (unit (fun x -> x > 10))
    )
    triv in
lower x
;;

(**if a relational noun is partial and bound into by a quantifier, the presupposition projects universally**)
let x = 
  let f = 
    let g = fun x ->
      match x with 
	| 1 -> 2
	| 2 -> 3 in
    unit g in
  lapply
    (up (rapply some triv))
    (rapply 
       lt
       (lapply (he 0) f)
    ) in
lower x
;;


let noo k s : ((e -> t) monad -> e) monad = 
  List.f
*)
