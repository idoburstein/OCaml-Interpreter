(*
                         OCaml Interpreter
                         Testing Evaluations
 *)

open CS51Utils ;;
open Absbook ;;

open Expr ;;
open Evaluation ;;
open Miniml ;;
open Env ;;


(* Testing free_vars *)
let tests_free_vars () =
  let num = 9 in
  assert (same_vars (free_vars (Num num)) (vars_of_list []));
  let l = "x" in
  let t = free_vars (Var l) in
  assert (same_vars t (vars_of_list [l]));
  let l = "x" in
  let t = free_vars (Conditional (Var l, Num 4, Num 5)) in
  assert (same_vars t (vars_of_list [l]));   
  let l = "y" in
  let t = free_vars (Let (l, Binop (Plus, Var l, Var l), 
                             Binop(Equals, Var l, Num 3))) in
  assert (same_vars t (vars_of_list [l])); 
  let l = "y" in
  let t = free_vars (App (Fun (l, Binop 
                                 (Plus, Var l, Var l)), Num 3)) in
  assert (same_vars t (vars_of_list []));  
  let y = "y" in
  let x = "x" in
  let exp1 = free_vars (App (Var x, Var y)) in
  assert (same_vars exp1 (vars_of_list [x; y])); 
  let x = "x" in
  let y = "y" in
  let exp1 = free_vars (Letrec(y, Binop (Times, Var x, Var x), Var x)) in
  let exp2 = free_vars (Letrec(x, Binop (Times, Var x, Var x), Var x)) in
  assert (same_vars exp1 (vars_of_list [x]));
  assert (same_vars exp2 (vars_of_list []));
  let x = "x" in
  let exp1 = free_vars (Let(x, Unop (Negate, Var x), Num 3)) in
  let exp2 = free_vars (Let(x, Unop (Negate, Num 3), Var x)) in
  assert (same_vars exp1 (vars_of_list [x]));
  assert (same_vars exp2 (vars_of_list []));
  () ;;   


(* Testing new_varname *)
let tests_new_varname () =
  let str = new_varname () in
  let str2 = new_varname () in
  let str3 = new_varname () in
  assert (str = "var0");
  assert (str2 = "var1");
  assert (str3 = "var2");
  () ;;


(* Testing subst *)
let tests_subst () =
  let num = 9 in
  assert (subst (string_of_int num) (Num 3) (Num num) = (Num num));
  assert (subst "x" (Num 3) (Binop (Plus, Var "x", Var "y")) = 
                             Binop (Plus, Num 3, Var "y"));
  assert (subst "y" (Num 3) (Binop (Plus, Var "x", Var "y")) = 
                             Binop (Plus, Var "x", Num 3));
  assert (subst "y" (Num 9) (Let ("x", Num 3, Binop 
                              (Division, Var "y", Var "x"))) = 
            Let ("x", Num 3, Binop (Division, Num 9, Var "x")));
  assert (subst "x" (Num 1) 
         (Conditional(Binop(LessThan, Var "x", Num 4), Num 1, Var "x")) = 
          Conditional(Binop(LessThan, Num 1, Num 4), Num 1, Num 1));
  assert (subst "x" (Num 10) (App (Var "x", Var "y")) = 
                              App (Num 10, Var "y"));
  assert (subst "y" (Num 1) (Fun ("x", Binop (Plus, Var "x", Var "y"))) =
                             Fun ("x", Binop (Plus, Var "x", Num 1)));
  assert (subst "x" (Num 7) (Letrec ("y", Var "x", 
                              Binop (Modulo, Var "x", Var "y"))) =
            Letrec ("y", Num 7, Binop (Modulo, Num 7, Var "y")));
            
   () ;;


(* Testing environment functions *)
let tests_env_functions () =
  let x = "x" in
  assert (close (Var x) (empty ()) = Closure (Var x, empty()));
  assert (env_to_string (empty ()) = "[ ]");
  let env1 = empty () in
  let var = "x" in
  let valu = ref (Val (Num 0)) in
  let env2 = extend env1 var valu in
  assert (lookup env2 var = Val (Num 0));
  assert (value_to_string (Val (Num 3)) = "3");
  assert (value_to_string (Closure ((Var "x"), (empty ()))) = "x where [ ]");
  () ;;   


(* tests for all evaluations *)
let similar_tests (f : (expr -> Env.env -> Env.value)) =
   unit_test (Env.value_to_string 
             (f (str_to_exp "9 ;;") 
             (Env.empty()) ) = "9") 
             "Testing num";
   unit_test (Env.value_to_string 
             (f (str_to_exp "if true > false then 1 else 0 ;;") 
             (Env.empty()) ) = "1") 
             "Testing bool and greater than";
   unit_test (Env.value_to_string 
             (f (str_to_exp "if 6 > 4 then 1 else ~-1 ;;") 
             (Env.empty()) ) = "1") 
             "Testing greater than";
   unit_test (Env.value_to_string 
             (f (str_to_exp "if 8 / 4 = 2 then 1 else ~-1 ;;") 
             (Env.empty()) ) = "1") 
             "Testing division"; 
   unit_test (Env.value_to_string 
             (f (str_to_exp "if 5 % 3 = 2 then 1 else ~-1 ;;") 
             (Env.empty()) ) = "1") 
             "Testing modulo"; 
   unit_test (Env.value_to_string 
             (f (str_to_exp " 7 * 6 ;;") 
             (Env.empty()) ) = "42") 
             "Testing times";
   unit_test (Env.value_to_string 
             (f (str_to_exp "(fun x -> x + x) 3 ;;") 
             (Env.empty()) ) = "6") 
             "Testing fun, app, binop";  
   unit_test (Env.value_to_string 
             (f (str_to_exp "10 - 5 ;;") 
             (Env.empty()) ) = "5") 
             "Testing binop minus";
   unit_test (Env.value_to_string 
             (f (str_to_exp "if 10 < 100 then 100 else 10 ;;") 
             (Env.empty()) ) = "100") 
             "Testing conditional and less than";
   unit_test (Env.value_to_string 
             (f (str_to_exp "let n = 3 in let f = fun x -> x * x in f (n - 1) ;;") 
             (Env.empty()) ) = "4") 
             "Testing let and fun and app";
   unit_test (Env.value_to_string 
             (f (str_to_exp "if true then 3 else 4 ;;") 
             (Env.empty()) ) = "3") 
             "Testing if";
   unit_test (Env.value_to_string 
             (f (str_to_exp ("let rec f = fun x -> if x < 2 " ^
                              "then 1 else x * f (x - 1) in f 5 ;;"))
             (Env.empty()) ) = "120") 
             "Testing let rec";
   unit_test (Env.value_to_string 
             (f (str_to_exp ("let rec f = fun x -> if x = 1 then 1 " ^
                              "else x * f (x - 1) in f 4 ;;"))
             (Env.empty()) ) = "24") 
             "Testing let rec 2";    
   () ;;

let distinct_lexical (f : (expr -> Env.env -> Env.value)) =
   unit_test (Env.value_to_string 
             (f (str_to_exp ("let x = 1 in let f = fun y -> x + y in " ^
                             "let x = 2 in f 3 ;;")) 
             (Env.empty()) ) = "4") 
   "Distinct testing lexical";
   unit_test (Env.value_to_string 
   (f (str_to_exp ("let x = 9 in let f = fun y -> x / y in " ^
                   "let x = 18 in f 3 ;;")) 
   (Env.empty()) ) = "3")  
   "Distinct testing lexical 2";
   () ;;

let distinct_dynamic (f : (expr -> Env.env -> Env.value)) =
   unit_test (Env.value_to_string 
   (f (str_to_exp ("let x = 1 in let f = fun y -> x + y in " ^
                   "let x = 2 in f 3 ;;")) 
   (Env.empty()) ) = "5")  
   "Distinct testing dynamic";
   unit_test (Env.value_to_string 
   (f (str_to_exp ("let x = 9 in let f = fun y -> x / y in " ^
                   "let x = 18 in f 3 ;;")) 
   (Env.empty()) ) = "6")  
   "Distinct testing dynamic 2";
   () ;;
   
 
 let _ = 
  tests_free_vars ();
  tests_new_varname ();
  tests_subst ();
  tests_env_functions ();
  similar_tests eval_s;
  similar_tests eval_d;
  similar_tests eval_l;
  distinct_dynamic eval_d; 
  distinct_lexical eval_s;
  distinct_lexical eval_l;
  ;;