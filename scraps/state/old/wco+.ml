(**state monad**)
let unit x = [fun s -> (x, s)];;

let unit' x = [fun s -> (x, x::s)];;

let bind =
  [fun x f s ->
    let (x',s') = x s in
    f x' s'];;

let pwfa f a = 
  List.concat 
    (List.map 
       (fun g -> (List.map g a)) f
    );;

let bind_pw x f = pwfa (pwfa bind x) f;;

(**the model, lexical entries/primitives**)
let univ = [1;2;3;4;5;6;7;8;9;10];;
