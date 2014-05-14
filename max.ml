type e = Boy1 | Boy2 | Boy3 | Boy4 | Boy5 | Boy6 | Boy7 
	 | Mov1 | Mov2 | Mov3 | Mov4 | Mov5 | Mov6 | Mov7;;
type ee = e list;;
type input = ee list;;
type output = input list;;
type prop = input -> output;;
type 'a cont = ('a -> prop) -> prop;;

let boys = [Boy1;Boy2;Boy3;Boy4;Boy5;Boy6;Boy7];;
let movs = [Mov1;Mov2;Mov3;Mov4;Mov5;Mov6;Mov7];;

let rec powerset = function
  | [] -> [[]]
  | h::t -> List.fold_left (fun xs t -> (h::t)::t::xs) [] (powerset t);;

let boyss = powerset boys;;
let movss = powerset movs;;

let saw (ys:ee) (xs:ee) : prop = fun s ->
  let see_base = [(Boy2,Mov2);(Boy3,Mov2);(Boy3,Mov3);(Boy3,Mov4);(Boy4,Mov4);(Boy4,Mov5);(Boy4,Mov6)] in
  let bool1 = List.for_all (fun x -> List.exists (fun y -> List.exists (fun z -> z = (x,y)) see_base) ys) xs in
  let bool2 = List.for_all (fun y -> List.exists (fun x -> List.exists (fun z -> z = (x,y)) see_base) xs) ys in
  if 
    bool1 & bool2 & List.length xs > 0 & List.length ys > 0
  then 
    [s] 
  else 
    []
;;

let max (pos:int) (output:output) : output =
  let rec target ls n = 
    match ls with 
      | [] -> n
      | x::xs -> 
	let ln = List.length (List.nth x pos) in 
	if ln > n
	then target xs ln
	else target xs n in 
  let filt x = List.length (List.nth x pos) >= target output 0 in
  List.filter filt output 
;;

let some p : ee cont = fun k s ->
  List.concat (List.map (fun x -> k x (List.concat [s;[x]])) p)
;;

let the_boys : ee cont = fun k s -> max 0 (some boyss k s);;
let the_movs : ee cont = fun k s -> max 1 (some movss k s);;

let card m n r : prop = fun s -> 
  List.filter (fun s -> List.length (List.nth s n) = m) (r s)
;;

let e3b : ee cont cont = fun k -> card 3 0 (k the_boys);;
let e5m : ee cont cont = fun k -> card 5 1 (k the_movs);;
let sawk : (ee -> ee -> prop) cont cont = fun k -> k (fun k' -> k' saw);;

let rap (m: ('a -> 'b) cont cont) (n: 'a cont cont) : 'b cont cont = fun k ->
  m (fun m' -> n (fun n' -> k (fun k' -> m' (fun f -> n' (fun x -> k' (f x))))))
;;

let lap (m: 'a cont cont) (n: ('a -> 'b) cont cont) : 'b cont cont = fun k ->
  m (fun m' -> n (fun n' -> k (fun k' -> m' (fun x -> n' (fun f -> k' (f x))))))
;;

let lower (m: prop cont cont) : 'a = m (fun m' -> m' (fun p -> p));;

(*exactly three boys saw exactly five movies*)
lower (lap e3b (rap sawk e5m)) [];;
(* - : output = [[[Boy2; Boy3; Boy4]; [Mov2; Mov3; Mov4; Mov5; Mov6]]]*)

let dist0 (m: (ee -> prop) cont cont) : (ee -> prop) cont cont = fun k -> 
  k (fun k' s -> 
    if List.for_all 
      (fun xs -> List.length 
	(m (fun m' -> m' (fun p -> k' (fun bye -> p [xs]))) s) > 0)
      (List.nth s 0)
    then [s]
    else []
  )
;;

(*dist reading should be true of `ex1 boy saw ex1 movie` -- viz. Boy2*)
let e1b : ee cont cont = fun k -> card 1 0 (k the_boys);;
let e1m : ee cont cont = fun k -> card 1 1 (k the_movs);;

(*yay!*)
lower (lap e1b (dist0 (rap sawk e1m))) [];;
(* - : output = [[[Boy2]]]*)
