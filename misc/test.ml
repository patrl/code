let univ = [1;2;3;4;5;6];;

let exists p = 
  let rec checker list = 
    match list with [] -> false
      | a::b -> 
	if p a = false 
	then checker b
	else true in
  checker univ;;

let forall p = 
  let rec checker list = 
    match list with [] -> true
      | a::b -> 
	if p a = false 
	then false
	else checker b in
  checker univ;;

let lift x = fun f -> f x;;
let int_lift f = fun c -> f (fun x -> c (fun k -> k x));;
let down f = f (fun x -> x);;
let down_3 f = fun c -> f (fun f' -> f' c);;
let down_4 f = fun c -> f (fun f' -> c (f' (fun x -> x)));;
let scope_f l r = fun c -> l (fun f -> r (fun x -> c (f x)));;
let scope_a l r = fun c -> l (fun x -> r (fun f -> c (f x)));;
let down x = x (fun f -> f);;
let tt_a l r = fun k -> l (fun l' -> r (fun r' -> k (fun c -> l' (fun x -> r' (fun f -> c (f x))))));;
let tt_f l r = fun k -> l (fun l' -> r (fun r' -> k (fun c -> l' (fun f -> r' (fun x -> c (f x))))));;

let likes x y = x = y;;

let so = fun c -> exists (fun x -> c x);;
let likes_3 = lift (lift likes);;
let eo = fun c -> forall (fun x -> c x);;

down (down_4 (tt_a (lift so) (tt_f likes_3 (int_lift eo))));;
