(* 
                         OCaml Interpreter
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
  | GreaterThan
  | Division
  | Modulo
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x -> 
      SS.singleton x 
  | Raise                     
  | Unassigned              
  | Num _                    
  | Bool _ -> 
      SS.empty                     
  | Unop (_neg, e1) -> 
      free_vars e1
  | App (e1, e2)
  | Binop (_, e1, e2) -> 
      SS.union (free_vars e1) (free_vars e2)     
  | Conditional (e1, e2, e3) -> 
      SS.union (SS.union (free_vars e1) (free_vars e2)) (free_vars e3) 
  | Fun (v, e1) -> 
      SS.remove v (free_vars e1) 
  | Let (v, e1, e2) -> 
      SS.union (SS.remove v (free_vars e2)) (free_vars e1)
  | Letrec (v, e1, e2) -> 
      SS.remove v (SS.union (free_vars e1) (free_vars e2))
  ;;

(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)

let new_varname : unit -> varid =
  let suffix = ref 0 in
  fun () -> let symbol = "var" ^ string_of_int !suffix in
             suffix := !suffix + 1;
             symbol ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)


(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Var x -> 
      if x = var_name then repl else exp                 
  | Raise                      
  | Unassigned
  | Bool _
  | Num _ -> 
      exp                                     
  | Unop (neg, e1) -> 
      Unop (neg, subst var_name repl e1)
  | Binop (opp, e1, e2) -> 
      Binop (opp, subst var_name repl e1, subst var_name repl e2)      
  | Conditional (e1, e2, e3) -> 
      Conditional(subst var_name repl e1, subst var_name repl e2, 
                                          subst var_name repl e3) 
  | Fun (v, e1) -> 
      if v = var_name then exp 
      else if not(SS.mem v (free_vars repl)) then Fun(v, subst var_name repl e1)
      else let new_v = new_varname () in
      Fun(new_v, subst var_name repl (subst v (Var new_v) e1))        
  | Let (v, e1, e2) ->  
      if v = var_name then Let(v, subst var_name repl e1, e2) 
      else if not(SS.mem v (free_vars repl)) 
      then Let(v, subst var_name repl e1, subst var_name repl e2)
      else let new_v = new_varname () in
      Let(new_v, subst var_name repl e1, 
                 subst var_name repl (subst v (Var new_v) e2))
  | Letrec (v, e1, e2) -> 
      if v = var_name then exp
      else if not(SS.mem v (free_vars repl)) 
      then Letrec(v, subst var_name repl e1, subst var_name repl e2)  
      else let new_v = new_varname () in
      Letrec(new_v, subst var_name repl (subst v (Var new_v) e1), 
      subst var_name repl (subst v (Var new_v) e2))                    
  | App (e1, e2) -> 
      App (subst var_name repl e1, subst var_name repl e2) ;;
     
(*......................................................................
  String representations of expressions
 *)
 
 
(* helper function for pattern matching *)
let match_binop (opp : binop) : string * string =
  match opp with
  | Plus -> " + ", "Binop(Plus ("
  | Minus -> " - ", "Binop(Minus ("
  | Times -> " * ", "Binop(Times ("
  | Equals -> " = ", "Binop(Equals ("
  | LessThan -> " < ", "Binop(LessThan ("
  | GreaterThan -> " > ", "Binop(GreaterThan ("
  | Division -> " / ", "Binop(Division ("
  | Modulo -> " % ", "Binop(Modulo ("
  ;;

(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var x -> 
      x                 
  | Num n -> 
      string_of_int n                     
  | Bool expr -> 
      string_of_bool expr                     
  | Unop (_neg, exp1) -> 
      "~- " ^ exp_to_concrete_string exp1  
  | Binop (opp, e1, e2) -> 
      exp_to_concrete_string e1 ^ fst (match_binop opp) ^ 
      exp_to_concrete_string e2      
  | Conditional (e1, e2, e3) -> 
      "if " ^ exp_to_concrete_string e1 ^ "then " ^ 
      exp_to_concrete_string e2 ^ "else " ^ exp_to_concrete_string e3    
  | Fun (var, exp) -> 
      "function " ^ var ^ "-> " ^ exp_to_concrete_string exp  
  | Let (v, e1, e2) -> 
      "let " ^ v ^ "= " ^ exp_to_concrete_string e1 ^ "in " ^ 
                          exp_to_concrete_string e2  
  | Letrec (v, e1, e2) -> 
      "let rec " ^ v ^ "= " ^ exp_to_concrete_string e1 ^ "in " ^ 
                              exp_to_concrete_string e2     
  | Raise -> 
      "Raise"                       
  | Unassigned -> 
      "Unassigned"                    
  | App (e1, e2) -> 
      exp_to_concrete_string e1 ^ " " ^ exp_to_concrete_string e2 
;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var x -> 
      "Var(" ^ x ^ ")"             
  | Num n -> 
      "Num(" ^ string_of_int n ^ ")"                    
  | Bool expr -> 
      "Bool(" ^ string_of_bool expr ^ ")"                     
  | Unop (_neg, exp1) -> 
      "Neg(" ^ exp_to_abstract_string exp1 ^ ")"  
  | Binop (opp, e1, e2) -> 
      snd (match_binop opp) ^ exp_to_abstract_string e1 ^ ", " ^ 
                              exp_to_abstract_string e2 ^ "))"      
  | Conditional (e1, e2, e3) -> 
      "Conditional(" ^ exp_to_abstract_string e1 ^ ", " ^ 
                       exp_to_abstract_string e2 ^ ", " ^ 
                       exp_to_abstract_string e3 ^ ")"   
  | Fun (var, exp) -> 
      "Fun(" ^ var ^ ", " ^ exp_to_abstract_string exp ^ ")" 
  | Let (v, e1, e2) -> 
      "Let(" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^ 
                          exp_to_abstract_string e2 ^ ")"  
  | Letrec (v, e1, e2) -> 
      "Letrec(" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^ 
                             exp_to_abstract_string e2 ^ ")"     
  | Raise -> 
      "Raise"                       
  | Unassigned -> 
      "Unassigned"                    
  | App (e1, e2) -> 
      "App(" ^ exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2 ^ ")"
;;
