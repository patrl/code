let univ = [1;2;3;4;5;6];;
let p0 = fun x -> true;;
let list_out = fun f x -> [f x];;
let pointwise op f a = 
  List.concat (List.map (fun f' -> (
    List.concat (List.map (list_out (op f')) a))) f);;
let dynand = fun p q i k -> (p i) (fun i' -> (q i' k));;
let fa f x = f x;;
let lift_e x = [fun p i k -> p x (x::i) k];;
let lift_et p = [fun x i k -> let a = (p x) in let b = (k i) in a & b];;
let lift_eet r = [fun x y i k -> let a = (r x y) in let b = (k i) in a & b];;
let dummy x p = if x = 0 then false else p;;
let runs = fun x -> dummy x (if (x = 1 or x = 3) then true else false);;
let man = fun x -> dummy x (if x > 3 then true else false);;
let woman = fun x -> dummy x (if man x then false else true);;
let left = fun x -> dummy x (if (x = 3 or x = 4 or x = 5) then true else false);;
let met = fun x y -> dummy x (dummy y (if (abs (y - x) < 2) then true else false));;
let likes = fun x y -> dummy x (dummy y (if (abs (y - x)) = 1 then true else false));;
let hates = fun x y -> dummy x (dummy y (if (abs (y - x)) = 2 then true else false));;
let and_ = pointwise dynand;;
let apply_ = pointwise fa;;

(*LOWERING*)
let k0 = fun i -> true;;
let i0 = [];;
let rec k00 list = match list with 
    [] -> true 
  | a::b -> (fun () -> k00 b)(print_int a);; 
let lower p = pointwise fa (pointwise fa p [[]]) [k00];;

(*QUANTIFICATION*)
(*Hendriks-style. Alternatively, we could further continuize the grammar or allow QR.*)
let ar_et p = fun s i k -> s p i k;;
let ar_eet r = fun o y i k -> o (fun x -> r x y) i k;;
let fc a b c = a (b c);;
let itv v = pointwise fa [ar_et] v;;
let sws v = pointwise fa [fun r o s i k -> fc ar_et (ar_eet r) o s i k] v;;
let ows v = pointwise fa [fun r o s i k -> ar_eet (fc ar_et r) o s i k] v;;

(*DYNAMIC BINDING; EXISTENTIALS*)
let some np = 
  let drefs = fun p -> 
    [fun x q i k ->
      if p x i (fun i' -> true) 
      then q x (x::i) k 
      else q 0 (0::i) k] 
  in pointwise fa (List.concat (List.map drefs np)) univ;;

let so = some (lift_et p0);;
let he n vp i k = vp (List.nth i (n-1)) i k;;

let somemanleft = pointwise fa (some (lift_et man)) (lift_et left);;
lower (and_ somemanleft (apply_ [he 1] (lift_et man)));;

(*NEGATION ; wipes out alternatives*)
let rec truths list = match list with 
    [] -> [] 
  | a::b -> if a = true then a::(truths b) else truths b;;
let neg p = [fun i k -> 
  let lower q = pointwise fa (pointwise fa q [i]) [fun i -> true] in
  if truths (lower p) = [] then true & k i else let a = false in let b = k i in a & b];;

lower (neg (apply_ so (lift_et left)));;
lower (and_ (neg (apply_ so (lift_et left))) (apply_ [he 1] (lift_et man)));;

(*MATERIAL IMPLICATION*)
let iffy p q = neg (and_ p (neg q));;
lower (iffy somemanleft (apply_ [he 1] (lift_et man)));;

let amanmetawoman = pointwise fa (pointwise fa (sws (lift_eet met)) (some (lift_et woman))) (some (lift_et man));;
let helikesher = pointwise fa (pointwise fa (sws (lift_eet likes)) [he 1]) [he 2];;
lower (iffy amanmetawoman helikesher);;

(*UNIVERSALS*)
let forall p = 
  let rec checker list prop = match list with
      [] -> true
    | a::b -> 
      if (prop a) = false 
      then false 
      else checker b prop in
  checker univ p;;

let every np vp = [fun i k -> 
  let persists list = if truths list = [] then false else true in 
  forall 
    (fun x -> 
      let lower q = pointwise fa (pointwise fa q [x::i]) [fun i -> true] in
      let restr = pointwise fa np [x] in 
      let scope = pointwise fa vp [x] in 
      let a = persists (lower (iffy restr scope)) in
      let b = k i in
      a & b)];;

(*RESTRICTED QUANTIFICATION, DONKEYS*)
let who = [fun ip n x i k -> n x i (fun i' -> ip (fun p i k -> p x i k) i' k)];;
let everymanwholeft = every (pointwise fa (pointwise fa who (pointwise fa [ar_et] (lift_et left))) (lift_et man));;
lower (everymanwholeft (lift_et left));;
lower (everymanwholeft (lift_et man));;
lower (everymanwholeft (lift_et woman));;

let somemanwholeft = some (pointwise fa (pointwise fa who (pointwise fa [ar_et] (lift_et left))) (lift_et man));;
lower (pointwise fa somemanwholeft (lift_et left));;
lower (pointwise fa somemanwholeft (lift_et man));;
lower (pointwise fa somemanwholeft (lift_et woman));;

let metawoman = pointwise fa (sws (lift_eet met)) (some (lift_et woman));;
let manwhometawoman = pointwise fa (pointwise fa who metawoman) (lift_et man);;
lower (every manwhometawoman (lift_et left));;
lower (every manwhometawoman (lift_et woman));;

let everymanwhometawomanlikesher = every manwhometawoman (pointwise fa (pointwise fa [ar_eet] (lift_eet likes)) [he 1]);;
lower everymanwhometawomanlikesher;;
let everymanwhometawomanhatesher = every manwhometawoman (pointwise fa (pointwise fa [ar_eet] (lift_eet hates)) [he 1]);;
lower everymanwhometawomanhatesher;;






(*
(*individual sentences*)
ar_et (lift_et runs) (some (lift_et man)) i0 k0;;
ar_et (lift_et runs) (every (lift_et man)) i0 k0;;
sws (lift_eet likes) eo so i0 k0;;
ows (lift_eet likes) eo so i0 k0;;

(*discourses*)
dynand (sws (lift_eet likes) eo so) (ar_et (lift_et runs) (some (lift_et man))) i0 k0;;
dynand (ows (lift_eet likes) eo so) (ar_et (lift_et runs) (some (lift_et man))) i0 k0;;

(*BINDING*)
let eq x y = x = y;;
let johnmethimself = sws (lift_eet met) (he 1) (lift_e 3);;
johnmethimself i0 k0;; (*nb: ows => presupposition failure*)
let everymanishimself = sws (lift_eet eq) (he 1) (every (lift_et man));;
everymanishimself i0 k0;;
let everymanleft = ar_et (lift_et left) (every (lift_et man));;
let everymanman = ar_et (lift_et man) (every (lift_et man));;
everymanleft i0 k0;;
let somemanmethimself = sws (lift_eet met) (he 1) (some (lift_et man));;
somemanishimself i0 k0;;

(*DYNAMIC BINDING/LACK THEREOF*)
(*john met himself. he left*)
dynand johnmethimself (he 1 (lift_et left)) i0 k0;;

(*some man met himself. he left.*)
dynand somemanmethimself (he 1 (lift_et left)) i0 k0;; 

(*every man is a man. he left.*)
(*"he" needs to be deictic; can't be fed the empty context*)
dynand everymanman (he 1 (lift_et left)) [] k0;; 

(*every man is himself. he left.*)
(*"he" needs to be deictic; can't be fed the empty context*)
dynand everymanishimself (he 1 (lift_et left)) [] k0;; 
*)
