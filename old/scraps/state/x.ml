type state = int list

type 'a monad = state -> (state -> 'a -> (bool*state) list) -> (bool*state) list

let unit (a:'a) : 'a monad = fun s k -> k s a

let bind (a:'a monad) (f:'a->'b monad) : 'b monad = 
  fun s k -> a s (fun s' x -> f x s' k)

let g = unit (fun x -> x <= 3);;

let lapply m h = bind m (fun x -> bind h (fun p -> unit (p x)));;
let rapply h m = bind h (fun p -> bind m (fun x -> unit (p x)));;

let lower (f:bool monad) = f [] (fun s k -> [(k,s)]);;

let x = lapply (unit 1) g in
lower x
;;

let x = rapply g (unit 1) in
lower x
;;

let eq = unit (fun (x:int) (y:int) -> x = y);;
let john : int monad = fun s k -> k (s@[1]) 1;;
let he n : int monad = fun s k -> k s (List.nth s n);;
let aman : int monad = fun s k -> List.concat [k (s@[1]) 1; k (s@[2]) 2];;
(*let some : ((int -> bool) -> int) monad = fun s k -> List.concat*) 

let x = lapply aman (rapply eq (he 0)) in
lower x
;;
