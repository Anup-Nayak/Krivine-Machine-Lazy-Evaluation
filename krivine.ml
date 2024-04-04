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

exception NOT_FOUND;;
exception TYPE_MISMATCH;;

type ans = N of int | B of bool | Pair of ans*ans | Closure of exp*((string*ans) list) ;;
type env = (string*ans) list;;

let rec lookup_var x env = match env with 
  | [] -> raise Not_found
  | (x',v) :: _ when x = x' -> v
  | _ :: rest -> lookup_var x rest


let rec stkmc focus stack = match focus, stack with
  (* unpacking *)
  | Closure(N n,t), [] -> N n
  | Closure(B b,t), [] -> B b
  (* lookup,abstraction,application  *)
  | Closure(V x,t), s  -> stkmc (lookup_var x t) s
  | Closure(Abs(x,e) ,t),(cl::s) -> stkmc (Closure(e,t@[(x,cl)])) s
  | Closure(App(e1,e2),t),s -> stkmc (Closure(e1,t)) ([Closure(e2,t)]@s)
  (* arithmetic & boolean operations *)
  | Closure(Plus(e1,e2),t), s -> (match ((stkmc (Closure(e1,t)) s) ,(stkmc (Closure(e2,t)) s)) with
                                  | (N n1, N n2) -> stkmc (Closure(N (n1+n2),t)) s 
                                  | _ -> raise TYPE_MISMATCH
                                  )
  | Closure(Times(e1,e2),t), s -> (match ((stkmc (Closure(e1,t)) s) ,(stkmc (Closure(e2,t)) s)) with
                                  | (N n1, N n2) -> stkmc (Closure(N (n1*n2),t)) s 
                                  | _ -> raise TYPE_MISMATCH
                                  )
  | Closure(And(e1,e2),t), s -> (match ((stkmc (Closure(e1,t)) s) ,(stkmc (Closure(e2,t)) s)) with
                                  | (B b1, B b2) -> stkmc (Closure(B (b1 && b2),t)) s 
                                  | _ -> raise TYPE_MISMATCH
                                  )
  | Closure(Or(e1,e2),t), s -> (match ((stkmc (Closure(e1,t)) s) ,(stkmc (Closure(e2,t)) s)) with
                                  | (B b1, B b2) -> stkmc (Closure(B (b1 || b2),t)) s 
                                  | _ -> raise TYPE_MISMATCH
                                  )
  | Closure(Not e, t), s -> (match (stkmc (Closure(e, t)) s) with
                                | B b -> stkmc (Closure(B (not b), t)) s
                                | _ -> raise TYPE_MISMATCH
                              )
  | Closure(Eq(e1, e2), t), s -> (match ((stkmc (Closure(e1,t)) s) ,(stkmc (Closure(e2,t)) s)) with
                                    | (N n1, N n2) -> stkmc (Closure(B (n1 = n2),t)) s 
                                    | _ -> raise TYPE_MISMATCH
                                  )
  | Closure(Gt(e1, e2), t), s -> (match ((stkmc (Closure(e1,t)) s) ,(stkmc (Closure(e2,t)) s)) with
                                    | (N n1, N n2) -> stkmc (Closure(B (n1 > n2),t)) s 
                                    | _ -> raise TYPE_MISMATCH
                                  )
  (* conditionals *)
  | Closure(IfTE(e1,e2,e3),t),s -> (match (stkmc (Closure(e1,t)) s) with
                                  | (B true) -> stkmc (Closure(e2,t)) s
                                  | (B false) -> stkmc (Closure(e3,t)) s
                                  | _ -> raise TYPE_MISMATCH
                                  )
  (* tuples, projections *)
  | Closure(Fst(e),t),s -> (match e with
                            | Pair(e1,e2) -> (stkmc (Closure(e1,t)) s)
                            | _ -> raise TYPE_MISMATCH
                            )
  | Closure(Snd(e),t),s -> (match e with
                            | Pair(e1,e2) -> (stkmc (Closure(e2,t)) s)
                            | _ -> raise TYPE_MISMATCH
                            )
  | Closure(Pair(e1,e2),t), s -> Pair((stkmc (Closure(e1,t)) s),(stkmc (Closure(e2,t)) s))
  
  | _ , _ -> raise NOT_FOUND