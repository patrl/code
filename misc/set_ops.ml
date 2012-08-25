
let univ = [1;2;3;4;5];;

let rec powerset = function
  | [] -> [[]]   
  | h::t ->
    List.fold_left (fun xs t -> (h::t)::t::xs) [] (powerset t)
;;

let rec insert x l = match l with
  | [] -> [[x]]
  | a::m -> (x::l) :: (List.map (fun y -> a::y) (insert x m))
;;

(* list of all permutations of l *)
let rec perms l = match l with
  | a::m -> List.flatten (List.map (insert a) (perms m))
  | _ -> [l]
;;

let rec mem list x = match list with 
  | [] -> false
  | a::b -> if x = a then true else mem b x;;

let rec remove list x = match list with 
  | [] -> []
  | a::b -> if x = a then b else a::(remove b x)
;;

let pplus = remove (powerset univ) [];;
