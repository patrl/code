(*regular recursive factorial*)
let rec factorial' n = 
  if n = 0 then 1 else
    n * (factorial' (n-1));;

(*tail recursive factorial*)
let factorial n = 
  let rec fact m n = 
    if m = 0 then n else
      fact (m-1) (m*n) in
  fact n 1;;

(*tail recursive length*)
let length' list = 
  let rec ll' list n = 
    match list with 
      | [] -> n
      | a::b -> ll' b (n+1) in
  ll' list 0;;

(*cps fib*)
let fibbo n = 
  let rec fib n k = match n with 
      0 -> k 0
    | 1 -> k 1
    | _ -> fib (n-1) (fun x -> fib (n-2) (fun y -> k (x+y))) in
  fib n (fun x -> x);;

(*cps fact*)
let facc n = 
  let rec fact n k = match n with 
      0 -> k 1
    | _ -> fact (n-1) (fun x -> k (x*n)) in
  fact n (fun x -> x);;


(*cps length*)
let length list = 
  let rec ll list k = match list with 
    | [] -> k 0
    | a::b -> ll b (fun x -> k (x+1)) in
  ll list (fun x -> x);;

