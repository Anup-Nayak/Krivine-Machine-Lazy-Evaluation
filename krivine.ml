(* DESIGN CHOICES *)
(* stkmc is a krivine + eval machine : clos*(clos list) -> clos -> ans *)
(* it does the unpacking within itself and returns the final answer *)
(* abstract machine runs eagerly, for eg (\x.(x+1))(20)  = 21 as per class notes *)

type exp = 
  N of int | B of bool
  | V of string
  | Plus of exp * exp | Times of exp * exp
  | And of exp * exp | Or of exp * exp | Not of exp
  | Eq of exp * exp | Gt of exp * exp  
  | IfTE of exp * exp * exp
  | Pair of exp * exp
  | Fst of exp | Snd of exp
  | Proj of exp list * int
  | Abs of string * exp | App of exp * exp
  ;;

exception NOT_FOUND;;
exception TYPE_MISMATCH;;
exception INVALID;;

type ans = N of int | B of bool | P of ans*ans | Closure of exp*((string*ans) list) ;;
type env = (string*ans) list;;

let rec lookup_var x env = match env with 
  | [] -> raise NOT_FOUND
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
  (* tuples *)
  | Closure(Pair(e1,e2),t), s -> (P(Closure(e1,t),Closure(e2,t)))
  | Closure(Fst e,t),s -> (match (stkmc (Closure(e,t)) s) with
                            | P(e1,e2) -> stkmc e1 s
                            | _ -> raise TYPE_MISMATCH
                            )
  | Closure(Snd e,t),s -> (match (stkmc (Closure(e,t)) s) with
                            | P(e1,e2) -> stkmc e2 s
                            | _ -> raise TYPE_MISMATCH
                            )
  
  (* projections *)
  | Closure(Proj(e,n),t), s -> (match (e,n) with
                                | ([],_) -> raise TYPE_MISMATCH
                                | (x::xs,0) -> stkmc (Closure(x,t)) s
                                | (x::xs,i) -> stkmc (Closure(Proj(xs,i-1),t)) s

  )
  | _ , _ -> raise INVALID


let test_cases = [

  (* Basic arithmetic and comparison *)
  (Closure(N 1,[]),[],N 1);
  (Closure(Plus(N 3,N 4),[]),[], N 7);
  (Closure(Times(N 8,N 9),[]),[], N 72);
  (Closure (Plus (N 3, N 4), []), [], N 7);
  (Closure (Times (N 8, N 9), []), [], N 72);
  (Closure (Eq (N 5, N 5), []), [], B true);
  (Closure (Eq (N 5, N 6), []), [], B false);
  (Closure (Gt (N 7, N 4), []), [], B true);
  (Closure (Gt (N 3, N 5), []), [], B false);

  (* Boolean expressions *)
  (Closure (And (B true, B true), []), [], B true);
  (Closure (And (B true, B false), []), [], B false);
  (Closure (Or (B false, B false), []), [], B false);
  (Closure (Or (B false, B true), []), [], B true);
  (Closure (Not (B true), []), [], B false);
  (Closure (Not (B false), []), [], B true);

  (* Conditional expressions *)
  (Closure (IfTE (B true, N 10, N 20), []), [], N 10);
  (Closure (IfTE (B false, N 10, N 20), []), [], N 20);

  (* Variables *)
  (Closure((V "x"), [("x", Closure(N 6,[]))]),[], N 6);
  (Closure (Plus (V "x", V "y"), [("x", Closure(N 6,[])); ("y", Closure(N 7,[]))]), [], N 13);
  (Closure (IfTE (V "x", V "y", V "z"), [("x", Closure(B true,[])); ("y", Closure(N 6,[])); ("z", Closure(N 7,[]))]), [], N 6);

  (* Pairs and projections *)
  (Closure(Pair (N 32, B true),[]),[],P (Closure(N 32,[]),Closure(B true,[])));
  (Closure (Pair (V "x", V "y"), [("x", Closure(N 42,[])); ("y", Closure(B true,[]))]), [], P (Closure(V "x",[("x", Closure(N 42,[])); ("y", Closure(B true,[]))]),Closure(V "y",[("x", Closure(N 42,[])); ("y", Closure(B true,[]))])));
  (Closure(Fst(Pair(N 42,B true)),[]),[],N 42);
  
  (Closure(Proj([V "x";V "y";V "z"],1),[("x",Closure(N 3,[]));("y",Closure(N 7,[]))]),[], N 7); 

  (* Test cases for abstraction *)
  (Closure (Abs ("x", Plus (V "x", N 20)), []), [Closure(N 1,[])], N 21);
  (Closure (Abs ("x", Plus (V "x", V "y")), [("y", Closure(N 5,[]))]), [Closure(N 1,[])], N 6);
  
  (* depicting lazy eval since x is not used in the function and hence it is not evaluated *)
  (Closure (Abs ("x", Abs ("y", V "y")), [("y",Closure(N 3,[]))]), [Closure(N 1,[]);Closure(N 2,[])], N 3);
  
  (* Test cases for application *)
  (Closure (App (Abs ("x", Plus (V "x", N 20)), N 5), []), [], N 25);
  (Closure (App (Abs ("x", Plus (V "x", V "y")), N 3), [("y", Closure(N 2,[]));("z", Closure(N 3,[]))]), [], N 5);
  (Closure (App (Abs ("x", Plus (V "x", V "y")), Plus (N 2, N 3)), [("y", Closure(N 5,[]))]), [], N 10);

  (* Error cases  *)
  (* change any of the above input/output *)

]
  
  
let rec run_tests cases = match cases with
  | [] -> print_endline "All test cases passed!"
  | (focus,stack,expected_result)::rest ->
      let result = stkmc focus stack in
        if result = expected_result then(
          print_endline "Test passed!";
          run_tests rest
        )else(
          print_endline "Test failed!";
        );;
  
  
  
run_tests test_cases;;