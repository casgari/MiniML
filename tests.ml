(* Tests for relevant functions in Expression and Evalution files *)

open Expr;;
open Evaluation;;

let test_exp_to_concrete_string () =
    assert (exp_to_concrete_string (Var "x") = "x");
    assert (exp_to_concrete_string (Num 3) = "3");
    assert (exp_to_concrete_string (Bool true) = "true");
    assert (exp_to_concrete_string (Unop (Negate, Var "x")) = "~-x");
    assert (exp_to_concrete_string (Binop (Plus, Var "x", Num 3)) = "x + 3");
    assert (exp_to_concrete_string (Raise) = "Raise");
    assert (exp_to_concrete_string (Unassigned) = "Unassigned");
    assert (exp_to_concrete_string (Conditional (Binop (LessThan, Var "x", Num 3), Num 3, Var "x")) 
                                    = "if x < 3 then 3 else x");
    assert (exp_to_concrete_string (Let ("x", Fun ("y", Var "x"), Var "x")) 
                                    = "let x = fun y -> x in x");
    assert (exp_to_concrete_string (Letrec ("x", Fun ("y", Var "x"), Var "x")) 
                                    = "let rec x = fun y -> x in x");
    assert (exp_to_concrete_string (Let ("z", Fun ("x", Binop (Plus, Num 3, Var "x")), App (Var "z", Num 3))) 
                                    = "let z = fun x -> 3 + x in z 3")
;;

let test_exp_to_abstract_string () =
    assert (exp_to_abstract_string (Var "x") = "Var(x)");
    assert (exp_to_abstract_string (Num 3) = "Num(3)");
    assert (exp_to_abstract_string (Bool true) = "Bool(true)");
    assert (exp_to_abstract_string (Unop (Negate, Var "x")) = "Unop(Negate, Var(x))");
    assert (exp_to_abstract_string (Binop (Plus, Var "x", Num 3)) = "Binop(Plus, Var(x), Num(3))");
    assert (exp_to_abstract_string (Raise) = "Raise");
    assert (exp_to_abstract_string (Unassigned) = "Unassigned");
    assert (exp_to_abstract_string (Conditional (Binop (LessThan, Var "x", Num 3), Num 3, Var "x")) 
                                    = "Conditional(Binop(LessThan, Var(x), Num(3)), Num(3), Var(x))");
    assert (exp_to_abstract_string (Let ("x", Fun ("y", Var "x"), Var "x")) 
                                    = "Let(x, Fun(y, Var(x)), Var(x))");
    assert (exp_to_abstract_string (Letrec ("x", Fun ("y", Var "x"), Var "x")) 
                                    = "Letrec(x, Fun(y, Var(x)), Var(x))");
    assert (exp_to_abstract_string (Let ("z", Fun ("x", Binop (Plus, Num 3, Var "x")), App (Var "z", Num 3))) 
                                    = "Let(z, Fun(x, Binop(Plus, Num(3), Var(x))), App(Var(z), Num(3)))")
;;

let test_free_vars () = 
    assert (same_vars (free_vars (Var "x")) (vars_of_list ["x"]));
    assert (same_vars (free_vars (Num 3)) (vars_of_list []));
    assert (same_vars (free_vars (Bool true)) (vars_of_list []));
    assert (same_vars (free_vars (Unop (Negate, Var "x"))) (vars_of_list ["x"]));
    assert (same_vars (free_vars (Binop (Plus, Var "x", Num 3))) (vars_of_list ["x"]));
    assert (same_vars (free_vars (Raise)) (vars_of_list []));
    assert (same_vars (free_vars (Conditional (Binop (LessThan, Var "x", Num 3), Num 3, Var "x"))) (vars_of_list ["x"]));
    assert (same_vars (free_vars (Let ("x", Fun ("y", Var "x"), Var "x"))) (vars_of_list ["x"]));
    assert (same_vars (free_vars (Letrec ("x", Fun ("y", Var "x"), Var "x"))) (vars_of_list []));
    assert (same_vars (free_vars (Let ("z", Fun ("x", Binop (Plus, Num 3, Var "x")), App (Var "z", Num 3)))) (vars_of_list []))    
  ;;

let test_subst () = 
    assert (subst "x" (Num 3) (Var "x") = Num 3);
    assert (subst "x" (Fun ("n", Var "n")) (Raise) = Raise);
    assert (subst "x" (Fun ("n", Var "n")) (Unassigned) = Unassigned);
    assert (subst "x" (Num 2) (Fun ("x", Var "x")) = (Fun ("x", Var "x")));
;;

let test_env () =
    let env = Env.empty () in
    assert (Env.close (Var "x") env = Closure (Var "x", env));
    let env = Env.extend env "x" (ref (Env.Val (Num 3))) in
    assert (Env.lookup env "x" = Env.Val (Num 3));
    assert (Env.value_to_string (Env.Val (Num 3)) = "3");
    assert (Env.env_to_string env = "(x -> 3); ")
;;

let test_eval_s () =
    let env = Env.empty () in
    assert(eval_s (Num 3) env = Env.Val (Num 3));
    assert(eval_s (Unop (Negate, Num 3)) env = Env.Val (Num ~-3));
    assert(eval_s (Binop (Times, Num 6, Num 7)) env = Env.Val (Num 42));
    assert(eval_s (Let ("f", Fun("x", Num 42), App (Var "f", Num 21))) env = Env.Val (Num 42));
    assert(eval_s (Let("f", Fun("x", Var "x"), App(App(Var "f", Var "f"), Num 3))) env = Env.Val (Num 3));
    assert(eval_s (Letrec("f", Fun("x", Conditional(Binop(Equals, Var "x", Num 0), Num 1,
                    Binop(Times, Var "x", App(Var "f", Binop(Minus, Var "x", Num 1))))),
                    App(Var "f", Num 4))) env = Env.Val (Num 24))
;;

let test_eval_d () =
    let env = Env.empty () in
    assert(eval_d (Num 3) env = Env.Val (Num 3));
    assert(eval_d (Unop (Negate, Num 3)) env = Env.Val (Num ~-3));
    assert(eval_d (Binop (Times, Num 6, Num 7)) env = Env.Val (Num 42));
    assert(eval_d (Let ("f", Fun("x", Num 42), App (Var "f", Num 21))) env = Env.Val (Num 42));
    assert(eval_d (Let("f", Fun("x", Var "x"), App(App(Var "f", Var "f"), Num 3))) env = Env.Val (Num 3));
    assert(eval_d (Letrec("f", Fun("x", Conditional(Binop(Equals, Var "x", Num 0), Num 1,
                    Binop(Times, Var "x", App(Var "f", Binop(Minus, Var "x", Num 1))))),
                    App(Var "f", Num 4))) env = Env.Val (Num 24));
    assert(eval_d (Let("x", Num 1, Let("f", Fun("y", Binop(Plus, Var "x", Var "y")), 
                    Let("x", Num(2), App(Var "f", Num 3))))) env = Env.Val (Num 5))
;;

let test_eval_l () =
    let env = Env.empty () in
    assert(eval_l (Num 3) env = Env.Val (Num 3));
    assert(eval_l (Unop (Negate, Num 3)) env = Env.Val (Num ~-3));
    assert(eval_l (Binop (Times, Num 6, Num 7)) env = Env.Val (Num 42));
    assert(eval_l (Let ("f", Fun("x", Num 42), App (Var "f", Num 21))) env = Env.Val (Num 42));
    assert(eval_l (Let("f", Fun("x", Var "x"), App(App(Var "f", Var "f"), Num 3))) env = Env.Val (Num 3));
    assert(eval_l (Letrec("f", Fun("x", Conditional(Binop(Equals, Var "x", Num 0), Num 1,
                    Binop(Times, Var "x", App(Var "f", Binop(Minus, Var "x", Num 1))))),
                    App(Var "f", Num 4))) env = Env.Val (Num 24));
    assert(eval_l (Let("x", Num 1, Let("f", Fun("y", Binop(Plus, Var "x", Var "y")), 
                    Let("x", Num(2), App(Var "f", Num 3))))) env = Env.Val (Num 4))
;;

let test () = 
    test_exp_to_concrete_string ();
    test_exp_to_abstract_string ();
    test_free_vars ();
    test_subst ();
    test_env ();
    test_eval_s ();
    test_eval_d ();
    test_eval_l ();
    ();;

let _ = test () ;;
