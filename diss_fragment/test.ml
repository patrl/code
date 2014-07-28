(**Lexicon/model**)
type e = Boy1 | Boy2 | Boy3 | Boy4 | Boy5 | Girl1 | Girl2 | Girl3 | Girl4 | Girl5;;
type t = bool;;
let dom = 
  [Boy1; Boy2; Boy3; Boy4; Boy5; Girl1; Girl2; Girl3; Girl4; Girl5];;
let thing x =
 List.exists (fun y -> y = x) dom;;
let boy x = 
  List.exists (fun y -> y = x) [Boy1; Boy2; Boy3; Boy4; Boy5];;
let girl x = 
  List.exists (fun y -> y = x) [Girl1; Girl2; Girl3; Girl4; Girl5];;
let left x = 
  List.exists (fun y -> y = x) [Boy1; Boy2; Boy3; Girl3; Girl4; Girl5];;
let likes y x =
  let base = [(Boy1, Girl1); (Boy1, Girl2); (Boy1, Girl3); (Boy1, Girl4);
	      (Boy1, Girl5); (Girl1, Boy1); (Girl2, Boy1)] in 
  List.exists (fun a -> a = (x, y)) base;;


(**State.Set monad**)
type 'a mon = (e list) -> ('a * e list) list;;
let inj (a: 'a) : 'a mon = 
  fun s -> [(a, s)];;
let seq (m: 'a mon) (k: 'a -> 'b mon) : 'b mon = 
  fun s -> 
    List.concat (List.map (fun (a, s') -> k a s') (m s));;


(**ContT applied to State.Set**)
type ('a, 'b) cont = ('a -> 'b mon) -> 'b mon;;
let lift (m: 'a mon) : ('a, 'b) cont = seq m;;
let up (a: 'a) : ('a, 'b) cont = lift (inj a);;
let int_up (m: ('a, 'b) cont) : (('a, 'c) cont, 'b) cont = 
  fun c -> m (fun a -> c (up a));;

(*2- and 3- level combination*)
let sa2 (m: ('a -> 'b, 'c) cont) (n: ('a, 'c) cont) : ('b, 'c) cont = 
  fun k -> m (fun x -> n (fun y -> k (x y)));;
let sb2 (m: ('a, 'c) cont) (n: ('a -> 'b, 'c) cont) : ('b, 'c) cont = 
  fun k -> m (fun x -> n (fun y -> k (y x)));;
let sa3 
    (m: (('a -> 'b, 'c) cont, 'd) cont)
    (n: (('a, 'c) cont, 'd) cont) : (('b, 'c) cont, 'd) cont = 
  fun k -> m (fun m' -> n (fun n' -> k (sa2 m' n')));;
let sb3 
    (m: (('a, 'c) cont, 'd) cont)
    (n: (('a -> 'b, 'c) cont, 'd) cont) : (('b, 'c) cont, 'd) cont = 
  fun k -> m (fun m' -> n (fun n' -> k (sb2 m' n')));;

(*infix versions*)
let (>>) = sa2;;
let (<<) = sb2;;
let (>>>) = sa3;;
let (<<<) = sb3;;

(*evaluation*)
let eval2 (m: ('a, 'a) cont) : 'a mon = 
  m inj;;
let eval3 (m: (('a, 'a) cont, 'a) cont) : 'a mon = 
  m (up inj);;
let eval3' (m: (('a, 'a) cont, 'a mon) cont) : 'a mon mon = 
  eval2 (up inj << m);;
let show m = m [];;
let display m = eval2 m [];;
let display' m = eval3 m [];;

(*Pronouns and binding*)
let pro : e mon = 
  let last s = List.nth s (List.length s - 1) in
  fun s -> [(last s, s)];;
let bind (m: ('a, 'b) cont) : ('a, 'b) cont = 
  fun k -> m (fun a s -> 
    k a (List.concat [s;[a]]));;

(*Some fancier entries*)
let some (np: e -> t mon) : e mon = fun s ->
  let helper x = 
    List.map 
      (fun (p, s') -> (x, s')) 
      (List.filter (fun (a, s') -> a) (np x s)) in 
  List.concat (List.map helper dom);;

let neg (p: t mon) : t mon = fun s -> 
  [(not (List.exists (fun (a, s') -> a) (p s)), s)];;

let cond (p: t mon) (q: t mon) : t mon =
  neg (seq p (fun p' -> seq (neg q) (fun q' -> inj (p' && q'))));;

let every (np: e -> t mon) : (e, t) cont = fun k ->
  neg (seq (some np) (fun x -> neg (k x)));;

(*DP meanings*)
let a_girl : e mon = 
  some (fun x -> inj (girl x));;
let a_boy : e mon = 
  some (fun x -> inj (boy x));;
let ev_boy : (e, t) cont = 
  every (fun x -> inj (boy x));;
let ev_girl : (e, t) cont = 
  every (fun x -> inj (girl x));;

(*a boy likes a girl*)
let a_boy_likes_a_girl = 
  bind (lift a_boy) << 
    (up likes >> bind (lift a_girl));;
let a_boy_likes_a_girl_eval = 
  eval2 a_boy_likes_a_girl;;
show a_boy_likes_a_girl_eval;;
