type e = int
type t = bool
type s = int list
type 'a monad = 
    ('a -> s -> (t * s) list) -> 
    s -> (t * s) list
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
  f (fun x s -> [(x,s)]) []
;;
let truthy (ls: (t * s) list) : bool = 
  List.exists (fun (a,b) -> a) ls
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
let triv : (e -> e -> t) monad = 
  unit (fun x y -> true)
;;

(*1 <= 3*)
let x = lapply one leq3 in
lower x
;;

(*some : restrictor must be pure : parallels B&S/Shan*)
let some : (e -> t) -> e monad = fun p k s ->
  List.concat 
    (List.map 
       (fun x -> k x (s@[x])) 
       (List.filter p univ)
    )
;;

(*some x = 3 / > 8 equals itself*)
let x = 
  lapply 
    (some (fun x -> x = 3 || x > 8))
    (rapply 
       eq 
       (he 0)
    ) in
lower x
;;

(*3 equals some x = 3*)
let x = 
  lapply 
    (unit 3)
    (rapply 
       eq 
       (some (fun x -> x = 3))
    ) in
lower x
;;

(*stack flattening : there must be a better way!*)
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
    if n = min_length list
    then drefs
    else match list with 
      | [] -> drefs
      | a::b ->
	let a_n = List.nth a n in
	if (is_common_at a_n list n)
	then checker list (a_n::drefs) (n+1) 
	else checker list drefs (n+1) in
  List.rev (checker (get_assignments list) [] 0);;

(*every : again, restrictor must be pure*)
let every : (e -> t) -> e monad = fun p k s ->
  let ls = 
    List.concat 
      (List.map 
	 (fun x -> k x (s@[x])) 
	 (List.filter p univ)
      ) in
  [(List.for_all (fun (a,b) -> a) ls, drefs_in_common ls)]
;;

(*every x = 3 / > 8 equals itself : no drefs project*)
let x = 
  lapply 
    (every (fun x -> x = 3 || x > 8))
    (rapply 
       eq 
       (he 0)
    ) in
lower x
;;

(*every x = 3 equals itself : dref projects*)
let x = 
  lapply 
    (every (fun x -> x = 3))
    (rapply 
       eq 
       (he 0)
    ) in
lower x
;;

(*everyone TRIVs some x = 3 : dref projects*)
let x = 
  lapply 
    (every (fun x -> true))
    (rapply 
       triv 
       (some (fun x -> x = 3))
    ) in
lower x
;;



(*3 level monad for doing quantification with impure restrictors*)
let lapply3 (m: 'a monad monad) (h: ('a -> 'b) monad monad) : 'b monad monad = 
  bind m 
    (fun x -> bind h 
      (fun f -> unit (lapply x f))
    )
;;
let rapply3 (h: ('a -> 'b) monad monad) (m: 'a monad monad) : 'b monad monad = 
  bind h 
    (fun f -> bind m 
      (fun x -> unit (rapply f x))
    )
;;
let lower3 (f: t monad monad) : (t*s) list = 
  f (fun x -> x (fun y s -> [(y,s)])) [];;

(*impure restrictors : some x <=3 <= 3*)
let x = 
  lapply3 
    (rapply 
       (unit some) 
       leq3
    ) 
    (unit leq3) in
lower3 x
;;

(*binding into impure restrictors?*)
