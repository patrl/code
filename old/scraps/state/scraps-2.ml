
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

(*binding into impure restrictors?
let some : ((e -> t) monad -> e) monad = fun k s ->
 List.concat 
    (List.map 
       (fun x -> k x (s@[x]))
       (List.filter p univ)
    )
;;*)


let truthy (ls: (t * s) list) : bool = 
  List.exists (fun (a,b) -> a) ls
;;
