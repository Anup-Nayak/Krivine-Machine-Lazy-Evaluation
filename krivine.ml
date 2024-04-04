(* DESIGN CHOICES *)
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

exception Not_found;;

type ans = N of int | B of bool | P of ans*ans | Closure of exp*((string*ans) list) ;;
type env = (string*ans) list;;

let rec lookup_var x env = match env with 
  | [] -> raise Not_found
  | (x',v) :: _ when x = x' -> v
  | _ :: rest -> lookup_var x rest

let unpack x = match x with
  | V y -> y
  | _ -> raise Not_found


let rec stkmc focus stack = match focus, stack with
  | Closure(N n,t), [] -> N n
  | Closure(B b,t), [] -> B b
  | Closure(V x,t), s  -> stkmc (lookup_var x t) s
  | Closure(Abs(x,e) ,t),(cl::s) -> stkmc (Closure(e,t@[(x,cl)])) s
  | Closure(App(e1,e2),t),s -> stkmc (Closure(e1,t)) ([Closure(e2,t)]@s)
  | Closure(Plus(e1,e2),t), s -> raise Not_found
  | _ , _ -> raise Not_found