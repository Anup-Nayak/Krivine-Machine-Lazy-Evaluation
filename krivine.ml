(* design choices *)
(* stkmc is a krivine + eval machine : clos*(clos list) -> clos -> ans, *)
(* it does the unpacking within itself and returns the final answer *)

type exp = N of int | B of bool
  | V of string
  | Plus of exp * exp | Times of exp * exp
  | And of exp * exp | Or of exp * exp | Not of exp
  | Eq of exp * exp | Gt of exp * exp  
  | IfTE of exp * exp *exp
  | Pair of exp * exp
  | Fst of exp | Snd of exp
  | Abs of string * exp | App of exp * exp
  ;;


type ans = N of int | B of bool | P of ans*ans | Closure of exp*((string*ans) list) ;;
type env = (string*ans) list;;

exception Not_found;;

let rec stkmc focus stack focus = match focus, stack with
  | Closure(N n,g), [] -> N n
  | Closure(B b,g), [] -> B b
  | Closure(V x,g), s  -> raise Not_found
  | _ , _ -> raise Not_found