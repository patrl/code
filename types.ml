type state = int list

type 'a monad = state -> ('a * state) list

let star (m:'a monad) (k:'a -> bool monad) : bool monad = fun s ->
  let ls = m s in
  let mapper = fun (a,b) -> k a b in
  List.concat (List.map mapper ls);;

let eta (a:'a) : 'a monad = fun s -> [(a,s)];;
