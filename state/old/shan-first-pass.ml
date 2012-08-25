let univ = [1;2;3;4;5;6;7;8;9];;
let unit x = fun (g : 'a list) -> [(g,x)];;
let rec excise list g =
  if list = g then [] else match list with 
      [] -> []
    | a::b -> if (b = g) then [a] else a::(excise b g);;
let bind f a = fun g ->
  let apply pair1 pair2 = 
    let (a,c) = pair1 in 
    let (b,d) = pair2 in
    if c(d) = [] then [] else
    [(let x = excise a g in let y = excise b g in List.concat [x;y;g], c(d))] in 
  let pwfa a b =
    List.concat (List.map (fun f -> List.concat (List.map (apply f) b)) a) in 
  pwfa (f g) (a g);;
let a = fun g -> List.map (fun x -> (x::g, fun p -> if (p [x]) = [()] then [x] else [])) univ;;
let man = fun list -> if (list = [1] or  list = [5]) then [()] else [];;
let boy = fun list -> if (list = [2] or list = [5] or list = [9]) then [()] else [];;
let cool = fun list -> if (list = [2]) then [] else [()];;

let manorboy = fun g -> List.concat[unit man g; unit boy g];;
bind a (unit boy) [];;
bind a manorboy [88;99];;
let amanisaboy = bind (unit boy) (bind a (unit man));;
let aboyiscool = bind (unit cool) (bind a (unit boy));;

let dynand p q = fun g -> 
  let conjoin pair1 pair2 = 
    let (a,c) = pair1 in 
    let (b,d) = pair2 in
    [(let x = excise a g in let y = excise b g in List.concat [x;y;g], [()])] in
  let pwfa a b =
    List.concat (List.map (fun f -> List.concat (List.map (conjoin f) b)) a) in 
  pwfa (p g) (q g);;

let dynor p q = fun g -> 
  List.concat [p g; q g];;

let he int = fun g -> 
  let lookup = fun a -> List.nth a int in
  

let not p = fun g -> 
  let negate pair = 
    let (a,b) = pair in 
    [
