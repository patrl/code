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


(** DERIVATIONS **)
(*a girl left*)
let a_girl_left = 
  bind (lift a_girl) << up left;;
let a_girl_left_eval = eval2 a_girl_left;;
show a_girl_left_eval;;

(*she left*)
let she_left = 
  lift pro << up left;;
let she_left_eval = eval2 she_left;;

(*if a girl left, she left*)
let if_a_girl_left_she_left = 
  cond a_girl_left_eval she_left_eval;;
show if_a_girl_left_she_left;;

(*a boy left*)
let a_boy_left = 
  bind (lift a_boy) << up left;;
let a_boy_left_eval = 
  eval2 a_boy_left;;
show a_boy_left_eval;;

(*every boy left*)
let ev_boy_left = 
  bind ev_boy << up left;;
let ev_boy_left_eval = 
  eval2 ev_boy_left;;
show ev_boy_left_eval;;

(*a boy likes a girl*)
let a_boy_likes_a_girl = 
  bind (lift a_boy) << 
    (up likes >> bind (lift a_girl));;
let a_boy_likes_a_girl_eval = 
  eval2 a_boy_likes_a_girl;;
show a_boy_likes_a_girl_eval;;

(*a girl likes a boy*)
let a_girl_likes_a_boy = 
  bind (lift a_girl) << 
    (up likes >> bind (lift a_boy));;
let a_girl_likes_a_boy_eval = 
  eval2 a_girl_likes_a_boy;;
show a_girl_likes_a_boy_eval;;

(*a boy likes every girl -- surface scope*)
let a_boy_likes_every_girl =
  lift a_boy << 
    (up likes >> ev_girl);;
let a_boy_likes_every_girl_eval =
  eval2 a_boy_likes_every_girl;;
show a_boy_likes_every_girl_eval;;

(*a boy likes every girl -- inv scope*)
let a_boy_likes_every_girl_inv = 
  up (bind (lift a_boy)) <<<
  (int_up (up likes >> ev_girl));;
let a_boy_likes_every_girl_inv_eval = 
  eval3  a_boy_likes_every_girl_inv;;
show a_boy_likes_every_girl_inv_eval;;

(*not: a boy left. inv scope after evaluation*)
let not_a_boy_left_inv =
  up not >> lift a_boy_left_eval;;
let not_a_boy_left_inv_eval = 
  eval2 not_a_boy_left_inv;;
show not_a_boy_left_inv_eval;;

(*not: a girl left. inv scope after evaluation*)
let not_a_girl_left_inv =
  up not >> lift a_girl_left_eval;;
let not_a_girl_left_inv_eval = 
  eval2 not_a_girl_left_inv;;
show not_a_girl_left_inv_eval;;

(*not: a boy likes a girl. unselective inv scope after evaluation*)
let not_a_boy_likes_a_girl_inv = 
  up not >> lift a_boy_likes_a_girl_eval;;
let not_a_boy_likes_a_girl_inv_eval = 
  eval2 not_a_boy_likes_a_girl_inv;;
show not_a_boy_likes_a_girl_inv_eval ;;

(*not: a girl likes a boy. unselective inv scope after evaluation*)
let not_a_girl_likes_a_boy_inv = 
  up not >> lift a_girl_likes_a_boy_eval;;
let not_a_girl_likes_a_boy_inv_eval = 
  eval2 not_a_girl_likes_a_boy_inv;;
show not_a_girl_likes_a_boy_inv_eval ;;

(*not: every boy left. no inv scope post-evaluation. i.e. true not false*)
let not_ev_boy_left_inv =
  up not >> lift ev_boy_left_eval;;
let not_ev_boy_left_inv_eval = 
  eval2 not_ev_boy_left_inv;;
show not_ev_boy_left_inv_eval;;


(**higher-order result types**)
let a_boy' : ((e, t) cont, t mon) cont = int_up (bind (lift a_boy));;
let a_girl' : ((e, t) cont, t mon) cont = up (bind (lift a_girl));;

let a_boy_likes_a_girl' : ((t, t) cont, t mon) cont = 
  a_boy' <<< ((up (up likes)) >>> a_girl');;

let a_boy_likes_a_girl'_eval = eval3' a_boy_likes_a_girl';;

(*not: a boy likes a girl: a-boy has scope over negation, a-girl under*)
(*should, does hold only of the boys who like no girls, i.e. 2345*)
let not_a_boy_likes_a_girl' = 
  up lift >> (up neg >> lift a_boy_likes_a_girl'_eval);;
let not_a_boy_likes_a_girl'_eval = eval3 not_a_boy_likes_a_girl';;
show not_a_boy_likes_a_girl'_eval;;


(*disjunction*)
let (++) (m: ('a, 'b) cont) (n: ('a, 'b) cont) : ('a, 'b) cont = 
  fun k s ->
    List.concat [m k s; n k s];;

(*disjoining Boy1 and Boy2*)
let b1_or_b2 = bind (up Boy1) ++ bind (up Boy2) ;;
let b1_or_b2_eval = eval2 b1_or_b2 ;;
show b1_or_b2_eval ;;

(*higher-order disjunction*)
let b1_b2_b5_flat : ((e, t) cont, t) cont = 
  (up (bind (up Boy1) ++ bind (up Boy2))) ++ (int_up (bind (up Boy5))) ;;

let b1_b2_b5_flat_left = 
  b1_b2_b5_flat <<< up (up left) ;;
let b1_b2_b5_flat_left_eval = 
  eval3 b1_b2_b5_flat_left ;;
show b1_b2_b5_flat_left_eval ;;

(*not: b1 or b2 or b5 left [unselective inv scope]*)
let not_b1_b2_b5_flat_left =
  up not >> lift b1_b2_b5_flat_left_eval;;
let not_b1_b2_b5_flat_left_eval =
  eval2 not_b1_b2_b5_flat_left;;
show not_b1_b2_b5_flat_left_eval;;

(*higher-order, same meaning as before, just different type*)
let b1_b2_b5_bumpy : ((e, t) cont, t mon) cont = 
  (up (bind (up Boy1) ++ bind (up Boy2))) ++ (int_up (bind (up Boy5))) ;;

let b1_b2_b5_bumpy_left = 
  b1_b2_b5_bumpy <<< up (up left);;
let b1_b2_b5_bumpy_left_eval = 
  eval3' b1_b2_b5_bumpy_left;;
show b1_b2_b5_bumpy_left_eval;;

(*not: b1 or b2 or b5 left [selective inv scope, i.e. either not [b1 or b2] or b5]*)
let not_b1_b2_b5_bumpy_left =
  up neg >> lift b1_b2_b5_bumpy_left_eval;;
let not_b1_b2_b5_bumpy_left_eval =
  eval3 (up lift >> not_b1_b2_b5_bumpy_left);;
show not_b1_b2_b5_bumpy_left_eval;;
