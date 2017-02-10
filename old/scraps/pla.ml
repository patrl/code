let univ = [1;2;3;4;5;6;7;8;9;10];;

type prop = int list list;;

let lift_p p = fun x s ->
  let p_p x e = p (x e) in
  let rec checker s = 
    match s with 
      | [] -> []
      | e::tail -> 
	if p_p x e
	then [e]::(checker tail)
	else checker tail in
  List.concat (checker s)
;;

let lift_r r = fun x y s ->
  let r_r x y e = r (x e) (y e) in
  let rec checker s = 
    match s with 
      | [] -> []
      | e::tail -> 
	if r_r x y e
	then [e]::(checker tail)
	else checker tail in
  List.concat (checker s)
;;

let x n e = List.nth e (List.length e - (n + 1));;
let up x = fun e -> x;;

let is_2 x s : prop = lift_p (fun x -> x = 2) x s;;
let is_3 = lift_p (fun x -> x = 3);;
let lthan = lift_r (fun x y -> y < x);;
let gthan = lift_r (fun x y -> y > x);;
let equals = lift_r (fun x y -> y = x);;

let truthy list = List.length list > 0;;

let some p q s = 
  let mapper p x = 
    if truthy (p x s)
    then List.map (fun e -> e@[x e]) (p x s)
    else [] in
  let s' = List.concat (List.map (mapper p) (List.map up univ)) in
  q (fun e -> List.nth e (List.length e - 1)) s'
;;

let neg p s = 
  let test e = if truthy (p [e]) then [] else [e] in 
  List.concat (List.map test s)
;;

let conj p q s = 
  p (q s);;

let every p q = neg (some p (fun x -> neg (q x)));;

(*some n < some m=3 = 2*)
conj (is_2 (x 0)) (some (fun x -> (some is_3 (gthan x))) is_2) [[]];;

(*etc*)
conj (is_3 (x 1)) (some (fun x -> (some is_3 (gthan x))) is_2) [[]];;

(*etc*)
conj (is_3 (x 0)) (some (fun x -> (some is_3 (gthan x))) is_2) [[]];;

(*etc*)
conj (is_2 (x 1)) (some (fun x -> (some is_3 (gthan x))) is_2) [[]];;

(*every n < some m=3 = n*)
every (fun x -> some is_3 (gthan x)) (equals (x 0)) [[7]];;

(*every n < some m=3 = m*)
every (fun x -> some is_3 (gthan x)) (equals (x 1)) [[7]];;
