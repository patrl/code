(*state.list monad*) 
let unit x = fun (a,b) -> [(x,(a,b))]
;;
let unit' x = fun (a,b) -> [(x,(x::a, b))]
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
(**logical bits**)

let conj = unit (fun p q -> p & q)
;;
 
let x n = fun (a,b) -> unit (List.nth a n) (a,b);;
let p n = fun (a,b) -> unit (List.nth b n a) (a,b);;

let p4 =
  let p_dref = fun a x -> x = List.nth a 0 in
  let p = fun (a,b) -> unit (fun x -> x = List.nth a 0) (a,b) in
   fun (a,b) -> p (a, p_dref::b)
;;

bapply 
  (bapply (unit' 3) p4) 
  (fapply 
     conj
     (bapply (unit' 4) (p 0))
  )
  ([],[])
;;
