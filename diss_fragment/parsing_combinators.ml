(*data structures*)
type terminal = string;;
type label = S | DP | NP | VP | PP | N;;
type input = string list;;
type parseTree =
  | Empty
  | Leaf of terminal
  | Branch of (label * (parseTree * parseTree));;
type parser = input -> (parseTree * input) list;;

(*monadic bits*)
let return a : parser = fun s -> [(a, s)];;
let (>>=) (m: parser) (k: parseTree -> parser) : parser = fun s ->
    List.concat (List.map (fun (a, s') -> k a s') (m s));;

(*zero and plus*)
let zero : parser = fun s -> [];;
let (++) (m: parser) (n: parser) : parser = fun s -> 
  List.concat [m s; n s];;

(*leaf and branch parsers*)
let leaf (c: string) : parser = fun s -> 
  match s with
    | [] -> []
    | x::xs ->
      if x = c 
      then [(Leaf x, xs)]
      else [];;
let branch (lab: label) (m: parser) (n: parser) : parser = 
  m >>= fun x -> 
  n >>= fun y -> 
  return (Branch (lab, (x, y)));;

(*the grammar*)
let det : parser = leaf "the" ++ leaf "a" ++ leaf "every";;
let verb : parser = leaf "owns" ++ leaf "beats" ++ leaf "sees";;
let pp: parser = leaf "inside";;
let n : parser = leaf "farmer" ++ leaf "donkey" ++ leaf "binoculars" ++ leaf "house";;
let np : parser = n ++ branch NP n pp;;
let dp : parser = branch DP det np;;
let vp : parser = leaf "left" ++ branch VP verb dp ++ branch VP (branch VP verb dp) pp;;
let s : parser = branch S dp vp;; 

let parse_debug (sentence: string) = 
  let tokenize s = 
    List.filter 
      (fun s -> not (s = "")) 
      (String.nsplit s " ") in
  s (tokenize sentence);;

let parse (sentence: string) = 
  List.concat (List.map
    (fun (a, s) -> 
      if List.length s = 0
      then [a]
      else [ ])
    (parse_debug sentence));;

parse "the donkey left";;
parse "the donkey owns every house";;
parse "every farmer sees the donkey inside";;
