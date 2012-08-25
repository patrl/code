(* calc1.ml: original calculator from Week7, enhanced with Booleans and Immutable Pairs *)

type term =
    Intconstant of int
  | Relation of term
  | Multiplication of (term * term)
  | Addition of (term * term)
  | Variable of char
  | Let of (char * term * term)
  | Iszero of term
  | If of (term * term * term)
  | Makepair of (term * term)
  | First of term
    ;;

    type expressed_value = 
	Int of int | Bool of bool | Pair of expressed_value * expressed_value;;
    type bound_value = expressed_value;;
    type assignment = (char * bound_value) list;;

    let rec eval (t : term) (g : assignment) = match t with
      Intconstant x -> Int x
    | Multiplication (t1, t2) ->
        (* we don't handle cases where the subterms don't evaluate to Ints *)
        let Int i1 = eval t1 g
        in let Int i2 = eval t2 g
        (* Multiplication (t1, t2) should evaluate to an Int *)
        in Int (i1 * i2)
    | Addition (t1, t2) ->
        let Int i1 = eval t1 g
        in let Int i2 = eval t2 g
        in Int (i1 + i2)
    | Variable (var) ->
        (* we don't handle cases where g doesn't bind var to any value *)
        List.assoc var g
    | Let (var_to_bind, t2, t3) ->
        (* evaluate t3 under a new assignment where var_to_bind has been bound to
           the result of evaluating t2 under the current assignment *)
        let value2 = eval t2 g
        in let g' = (var_to_bind, value2) :: g
        in eval t3 g'
    | Iszero (t1) ->
        (* we don't handle cases where t1 doesn't evaluate to an Int *)
        let Int i1 = eval t1 g
        (* Iszero t1 should evaluate to a Bool *)
        in Bool (i1 = 0)
    | If (t1, t2, t3) ->
        (* we don't handle cases where t1 doesn't evaluate to a boolean *)
        let Bool b1 = eval t1 g
        in if b1 then eval t2 g
        else eval t3 g
    | Makepair (t1, t2) ->
        let value1 = eval t1 g
        in let value2 = eval t2 g
        in Pair (value1, value2)
    | First (t1) ->
        (* we don't handle cases where t1 doesn't evaluate to a Pair *)
        let Pair (value1, value2) = eval t1 g
        in value1
    ;;
