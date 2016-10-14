let unit x = fun k -> k x;;
let bind m f = fun k -> m (fun x -> f x k);;
let lower m = m (fun x s -> [(x,s)]);;
let reset m k s = List.concat (List.map (fun (a,b) -> k a b) (lower m s));;
let reset' m k s = List.concat (List.map (fun (a,b) -> k (reset a) b) (lower m s));;
let int_lift m c = m (fun x -> c (fun k -> k x));;
let int_lower m k = m (fun m' -> m' k);;

let univ = [1;2;3;4;5;6;7;8;9;10];;
let eq = unit (=);;
let geq = unit (fun x y -> y >= x);;
let leq = unit (fun x y -> y <= x);;

let one = unit 1;;
let two = unit 2;;
let it n k s = k (List.nth s n) s;; 

let lapply m f = bind m (fun x -> bind f (fun p -> unit (p x)));;
let rapply f m = bind f (fun p -> bind m (fun x -> unit (p x)));;
let lapply' m f = bind m (fun x -> bind f (fun p -> unit (lapply x p)));;
let rapply' m f = bind f (fun p -> bind m (fun x -> unit (rapply p x)));;


let some p k s = 
  let mapper x =
    List.filter 
      (fun (a,b) -> a) (lower (rapply p (unit x)) s) in
  List.concat
    (List.concat 
       (List.map (fun x -> List.map (fun (a,b) -> k x b) (mapper x)) univ))
;;

let up m = fun k -> m (fun x s -> k x (s@[x]));;

lower (up (some (rapply leq two))) [];;

let conj_f ls s = (List.for_all (fun (a,b) -> a) ls, s);;
let disj_f ls s = (List.exists (fun (a,b) -> a) ls, s);;

let every p k s = 
  let mapper x =
    List.filter 
      (fun (a,b) -> a) (lower (rapply p (unit x)) s) in
  [conj_f
    (List.concat 
       (List.map (fun x -> List.map (fun (a,b) -> disj_f (k x b) s) (mapper x)) univ))
    s]
  ;;

lower 
  (lapply 
     (up (every
	(rapply leq (unit 10))))
     (rapply
	eq 
	(up (every 
	   (rapply eq (it 0)))))
  ) [];;

lower 
  (lapply 
     (up (every
	(rapply leq (unit 10))))
     (rapply
	eq 
	(up (some 
	   (rapply leq (unit 10))))
     )
  ) [];;

lower 
  (lapply 
     (every
	(rapply leq (up (some (rapply leq (unit 10))))))
     (rapply
	leq
	(it 0)
     )
  ) [];;

lower 
  (int_lower 
     (reset'
	(lapply' 
	   (int_lift (up (some (rapply geq one)))) 
	   (unit (rapply eq one)))
     )
  ) [];;

lower 
  (lapply
     (up (some (rapply leq (unit 2))))
     (rapply 
	eq (up (some (rapply leq (unit 2))))
     )
  ) [];;
