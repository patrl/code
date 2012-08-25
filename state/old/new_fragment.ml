let p0 x = x < 4;;
let p1 x = x >= 4;;
let r0 x y = x = y;;
let r1 x y = y < x;;

type state = int list;;
let unit x = fun (s:state) -> (x, s);;
let unit' x = fun (s:state) -> (x, x::s);;
let bind x f = fun (s:state) -> 
  let (x', s') = x s in 
  let (x'', s'') = f x' s' in 
  (x'', s'');;

let lapply f x = bind f (fun f' -> bind x (fun x' -> unit (f' x')));;
let rapply f x = bind x (fun x' -> bind f (fun f' -> unit (f' x')));;

(*derived from slash directions*)
let lift1 p = fun u -> lapply (unit p) u;;
let lift2 r = fun u v -> rapply (lapply (unit r) u) v;;

let he n = fun (s:state) -> (List.nth s n, s);;
let succ x = x + 1;;

(*crossover*)
lift2 r1 (lift1 succ (he 0)) (unit' 1) [];;
(*undefined:
lift2 r1 (unit' 1) (lift1 succ (he 0)) [];;
*)

(*BOOD -- c-command irrelevant*)
lift2 r1 (he 0) (lift1 succ (unit' 1)) [];;

(*conjunction*)
let conj p q = bind p (fun p' -> bind q (fun q' -> unit (p' & q')));;

(*cross-sentential binding w/o c-command*)
conj (lift1 p0 (unit' 1)) (lift1 p0 (he 0)) [];;
