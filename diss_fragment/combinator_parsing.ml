(*data structures*)
type terminal = string;;
type label = string;;
type input = string list;;
type parseTree =
  | Leaf of terminal
  | Unary of (label * parseTree)
  | Binary of (label * (parseTree * parseTree));;
type parser = input -> (parseTree * input) list;;

(*monadic bits*)
let return a : parser = fun s -> [(a, s)];;
let (>>=) (m: parser) (k: parseTree -> parser) : parser = fun s ->
    List.concat (List.map (fun (a, s') -> k a s') (m s));;

(*zero and plus*)
let zero : parser = fun s -> [];;
let (++) (m: parser) (n: parser) : parser = fun s -> 
  List.concat [m s; n s];;

(*leaf, unary, binary parsers*)
let leaf (c: string) : parser = fun s -> 
  match s with
    | [] -> []
    | x::xs ->
      if x = c 
      then [(Leaf x, xs)]
      else [];;
let unary (lab: label) (m: parser) = 
  m >>= fun x -> 
  return (Unary (lab, x));;
let binary (lab: label) (m: parser) (n: parser) : parser = 
  m >>= fun x -> 
  n >>= fun y -> 
  return (Binary (lab, (x, y)));;

(*the grammar*)
let det : parser = 
  leaf "the" 
	 ++ leaf "a" 
	 ++ leaf "every";;
let verb : parser = 
  leaf "owns" 
	 ++ leaf "beats" 
	 ++ leaf "sees";;
let ditrans : parser =
  leaf "gives" 
	 ++ leaf "shows";;
let pp: parser = 
  leaf "inside";;
let n : parser = 
  leaf "farmer"
	 ++ leaf "donkey"
	 ++ leaf "binoculars"
	 ++ leaf "house";;
let np : parser = 
  n ++ binary "NP" n pp;;
let dp : parser = 
  leaf "Simon" ++ leaf "Matt" ++ binary "DP" det np;;
let vp : parser = 
  leaf "left" 
	 ++ binary "VP" verb dp 
	 ++ binary "VP" (binary "VP" verb dp) pp 
	 ++ binary "VP" (binary "VP" ditrans dp) dp
	 ++ binary "VP" (leaf "is") dp;;
let s : parser = binary "S" dp vp;; 

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

let tdl () = parse "the donkey left";;
let tdoeh () = parse "the donkey owns every house";;
let edbtfi () = parse "every donkey beats the farmer inside";;
let ssadtf () = parse "Simon shows a donkey the farmer"

let texify ps : unit list = 
  let rec helper p = match p with 
    | Leaf s -> s
    | Unary (lab, tree) -> "[." ^ lab ^ " " ^ helper tree ^ "] "
    | Binary (lab, (left, right)) ->
      "[." ^ lab ^ " " ^ helper left ^ " " ^ helper right ^ " ]" in
  List.map (fun p -> print_string ("\\Tree " ^ helper p ^ "\n" )) ps
;;

let a () = texify (tdl ());;
let b () = texify (tdoeh ());;
let c () = texify (edbtfi ());;
let d () = texify (ssadtf ());;
