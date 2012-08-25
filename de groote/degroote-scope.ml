let univ = [1;2;3;4;5;6];;
let k0 = fun i -> true;;
let i0 = [];;
let p0 = fun x -> true;;
let list_out = fun f x -> [f x];;
let dynand = fun p q i k -> (p i) (fun i' -> (q i' k));;
let lift_e = fun x p i k -> p x (x::i) k;;
let lift_et = fun p x i k -> (p x) & (k i);;
let lift_eet = fun r x y i k -> (r x y) & (k i);;
let runs = fun x -> if (x = 1 or x = 3) then true else false;;
let man = fun x -> if x > 2 then true else false;;
let woman = fun x -> if man x then false else true;;
let left = fun x -> if (x = 3 or x = 4 or x = 5) then true else false;;
let met = fun x y -> if (abs (y - x) < 2) then true else false;;
let likes = fun x y -> if (abs (y - x)) = 1 then true else false;;
let hates = fun x y -> if y = 3 then true else false;;
let r1 = lift_eet (fun x y -> x < y);;

(*QUANTIFICATION*)
(*Hendriks-style. Alternatively, we could further continuize the grammar or allow QR.*)
let ar_et p = fun s i k -> s p i k;;
let ar_eet r = fun o y i k -> o (fun x -> r x y) i k;;
let fc a b c = a (b c);;
let sws r o s i k = fc ar_et (ar_eet r) o s i k;;
let ows r o s i k = ar_eet (fc ar_et r) o s i k;;

let forall p = 
  let rec checker list prop = match list with
      [] -> true
    | a::b -> 
      if (prop a) = false 
      then false 
      else checker b prop in
  checker univ p ;;

let exists p = 
  let rec checker list prop = match list with
      [] -> false
    | a::b -> 
      if (prop a) = true 
      then true 
      else checker b prop in
  checker univ p ;;

let every2 np vp i k = 
  forall (fun x -> (not (np x i (fun i' -> true))) || (vp x (x::i) (fun i' -> true))) & k i;;

let every np vp i k = 
  forall (fun x -> 
    not (np x i (fun i' -> (not (vp x (x::i') (fun i'' -> true)))))) 
  & k i;;

let some np vp i k = 
  exists (fun x -> 
    np x i (fun i' -> vp x (x::i') k));;

let eo = every (lift_et p0);;
let so = some (lift_et p0);;

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
let he n vp i k = vp (List.nth i (n-1)) i k;;
let johnmethimself = sws (lift_eet met) (he 1) (lift_e 3);;
johnmethimself i0 k0;; (*nb: ows => presupposition failure*)
let everymanishimself = sws (lift_eet eq) (he 1) (every (lift_et man));;
everymanishimself i0 k0;;
let everymanleft = ar_et (lift_et left) (every (lift_et man));;
let everymanman = ar_et (lift_et man) (every (lift_et man));;
everymanleft i0 k0;;
let everymanmethimself = sws (lift_eet met) (he 1) (every (lift_et man));;
everymanmethimself i0 k0;;
let somemanmethimself = sws (lift_eet met) (he 1) (some (lift_et man));;
somemanmethimself i0 k0;;

(*CROSSOVER*)
let hemeteveryman = sws (lift_eet met) (every (lift_et man)) (he 1);;
hemeteveryman i0 k0;;
let hemeteveryman2 = ows (lift_eet met) (every (lift_et man)) (he 1);;
hemeteveryman2 i0 k0;;

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

(*RESTRICTED QUANTIFICATION, DONKEYS*)
let who ip n x i k = n x i (fun i' -> ip (fun p i k -> p x i k) i' k);;
let metawoman = sws (lift_eet met) (some (lift_et woman));;

(*every man who met a woman left*)
every (who metawoman (lift_et man)) (lift_et left) i0 k0;;

(*every man who met a woman likes himself*)
sws (lift_eet likes) (he 1) (every (who metawoman (lift_et man))) i0 k0;;

(*every man who met a woman likes her*)
sws (lift_eet likes) (he 2) (every (who metawoman (lift_et man))) i0 k0;;

(*MATERIAL IMPLICATION*)
let nah p i k = not (p i k0) & k i;;
let iffy p q i k = nah (dynand p (nah q)) i (fun i' -> true) & k i;;

(*if someone left he's a man*)
iffy (ar_et (lift_et left) so) (ar_et (lift_et man) (he 1)) i0 k0;;

(*if someone left she's a woman*)
iffy (ar_et (lift_et left) so) (ar_et (lift_et woman) (he 1)) i0 k0;;

(*if everyone exists, he's a man*)
(*interesting note here: ocaml's interpreter is lazy, so if p is false, it'll just return true regardless of whether q throws an exception or not (similarly for a conjunction: if the first sentence is false, it'll just return false). so the interpreter implements incremental strong kleene a la ben george. took a long time to figure out this was fucking stuff up!*)
iffy (ar_et (lift_et p0) eo) (ar_et (lift_et woman) (he 1)) i0 k0;;

(*E>A NECESSARY FOR DYNAMIC BINDING*)
(*there's someeone who hates everyone. he runs. [true]*)
dynand (sws (lift_eet hates) eo so) (ar_et (lift_et runs) (he 1)) i0 k0;;

(*there's someone who's hated by everyone. he runs. [false]*)
dynand (ows (lift_eet hates) so eo) (ar_et (lift_et runs) (he 1)) i0 k0;;

(*everyone likes someone or other. he runs. [#]*)
dynand (sws (lift_eet likes) so eo) (ar_et (lift_et runs) (he 1)) i0 k0;;

(*everyone's liked by someone or other. he runs [#]*)
dynand (ows (lift_eet likes) eo so) (ar_et (lift_et runs) (he 1)) i0 k0;;


(*inverse linking*)
sws r1 (he 2) (ar_eet (fun x -> some (r1 x)) (every2 (lift_et (fun x -> x < 6)))) i0 k0;;
(*i.e. the inv linked reading of some number above every non-maximal number is above it*)
