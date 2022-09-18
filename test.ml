(* Test file for testing functions *)

open Expr ;;
open Evaluation ;;

open CS51Utils ;;
open Absbook ;;

let free_vars_test () =
  unit_test (same_vars
            (free_vars (Let ("x", 
                   Binop (Plus, Var "x", Var "y"),
                   Binop (Times, Var "z", Num 3))))
            (vars_of_list ["x"; "y"; "z"])) "free variables let";
  unit_test (same_vars
            (free_vars (Fun ("x",
                      Binop (Plus, Var "x", Var "y"))))
            (vars_of_list ["y"])) "free variables fun";
  unit_test (same_vars
            (free_vars (Bool(false)))
            (vars_of_list [])) "free variables bool";
  unit_test (same_vars
            (free_vars (Var("x")))
            (vars_of_list ["x"])) "free variables variable";
  unit_test (same_vars
            (free_vars (Conditional (Bool(false),
                                    Binop(Minus, Var "y", Var "y"),
                                    Unop(Negate, Var "x"))))
            (vars_of_list ["x"; "y"])) "free variables conditional";
  ;;

let subst_test () =
  unit_test (subst "y" (Num 5)
                  (Binop (Plus, Num 2, Var "y"))
                = Binop (Plus, Num 2, Num 5))
                  "substitution simple operations";
  unit_test (subst "y" (Num 5) 
                  (Let ("x", 
                  Binop (Plus, Var "x", Var "y"),
                  Binop (Times, Var "z", Num 3)))
                = (Let ("x", 
                  Binop (Plus, Var "x", Num 5),
                  Binop (Times, Var "z", Num 3))))
                  "substitution trivial let";
  unit_test (subst "x" (Num 5)
                  (App (Var "x", Unop (Negate, Var "x")))
                = App (Num 5, Unop (Negate, Num 5)))
                  "substitution application";
  unit_test (subst "x" (Num 5)
                  (Fun ("x", Binop(Minus, Var "x", Num 3)))
                = Fun ("x", Binop(Minus, Var "x", Num 3)))
                  "substition same varname fun";
  unit_test (subst "x" (Var "y")
                  (Let ("y",
                        Binop(Plus, Var "x", Var "z"),
                        Binop(Times, Var "x", Var "y")))
                = (Let ("var1",
                        Binop(Plus, Var "y", Var "z"),
                        Binop(Times, Var "y", Var "var1"))))
                  "substitution binded let";
  ;;

let eval_s_test () =
  (* 5 + ~- 3 *)
  unit_test (eval_s (Binop(Plus, Num 5, Unop (Negate, Num 3))) 
                    (Env.empty ())
                    = Env.Val (Num 2)) 
                    "evaluation substitution arithmetics" ;
  (* let x = 5 in if x < 4 then 42 else false 
  (In our language this is POSSIBLE) *)
  unit_test (eval_s (Let("x", 
                        Num 5, 
                        Conditional (Binop (LessThan, Var "x", Num 4),
                                    Num 42,
                                    Bool false))) 
                    (Env.empty ()) 
                    = Env.Val (Bool false))
                    "evaluation substitution conditional" ;
  (* fun x -> 3 *)
  unit_test (eval_s (Fun ("x", Num 3))
                    (Env.empty ())
                    = Env.Val (Fun ("x", Num 3)))
                    "evaluation substitution function" ;
  (* (fun x -> x * 5) 3 *)
  unit_test (eval_s (App (Fun ("x", Binop (Times, Var "x", Num 5)),
                          Num 3))
                    (Env.empty ())
                    = Env.Val (Num 15))
                    "evaluation substitution function application" ;
  (* let rec x = fun y -> if y < 0 then y else x (y-1) in x 7 *)
  unit_test (eval_s (Letrec ("x",
                            Fun ("y", 
                                Conditional (Binop (LessThan, Var "y", Num 0),
                                            Var "y",
                                            App (Var "x", 
                                                Binop (Minus, 
                                                      Var "y", 
                                                      Num 1)))),
                            App (Var "x", Num 7)))
                    (Env.empty ())
                    = Env.Val (Num ~-1))
                    "evaluation substitution recursive function" ;

  (* let x = 5 in let f = fun y -> (x + y) in let x = 3 in f 2 *)
  unit_test (eval_s (Let ("x",
                          Num 5,
                          Let ("f",
                              Fun ("y", Binop(Plus, Var "x", Var "y")),
                              Let ("x",
                                  Num 3,
                                  App (Var "f", Num 2)))))
                    (Env.empty ())
                    = Env.Val (Num 7))
                    "evaluation substitution changing variable" ;
  ;;

(* Similiar tests as for eval_s *)
let eval_d_test () =
    (* 5 + ~- 3 *)
    unit_test (eval_d (Binop(Plus, Num 5, Unop (Negate, Num 3))) 
                      (Env.empty ())
                      = Env.Val (Num 2)) 
                      "evaluation dynamics arithmetics" ;
    (* let x = 5 in if x < 4 then 42 else false 
    (In our language this is POSSIBLE) *)
    unit_test (eval_d (Let("x", 
                          Num 5, 
                          Conditional (Binop (LessThan, Var "x", Num 4),
                                      Num 42,
                                      Bool false))) 
                      (Env.empty ()) 
                      = Env.Val (Bool false))
                      "evaluation dynamics conditional" ;
    (* fun x -> 3 *)
    unit_test (eval_d (Fun ("x", Num 3))
                      (Env.empty ())
                      = Env.Val (Fun ("x", Num 3)))
                      "evaluation dynamics function" ;
    (* (fun x -> x * 5) 3 *)
    unit_test (eval_d (App (Fun ("x", Binop (Times, Var "x", Num 5)),
                            Num 3))
                      (Env.empty ())
                      = Env.Val (Num 15))
                      "evaluation dynamics function application" ;
    (* let rec x = fun y -> if y < 0 then y else x (y-1) in x 7 *)
    unit_test (eval_d (Letrec ("x",
                              Fun ("y", 
                                  Conditional (Binop (LessThan, Var "y", Num 0),
                                              Var "y",
                                              App (Var "x", 
                                                  Binop (Minus, 
                                                        Var "y", 
                                                        Num 1)))),
                              App (Var "x", Num 7)))
                      (Env.empty ())
                      = Env.Val (Num ~-1))
                      "evaluation dynamics recursive function" ;
    (* let x = 5 in let f = fun y -> (x + y) in let x = 3 in f 2 *)
    unit_test (eval_d (Let ("x",
                            Num 5,
                            Let ("f",
                                Fun ("y", Binop(Plus, Var "x", Var "y")),
                                Let ("x",
                                    Num 3,
                                    App (Var "f", Num 2)))))
                      (Env.empty ())
                      = Env.Val (Num 5))
                      "evaluation dynamics changing variable" ;
    ;;

let eval_l_test () =
  (* 5 + ~- 3 *)
  unit_test (eval_l (Binop(Plus, Num 5, Unop (Negate, Num 3))) 
                    (Env.empty ())
                    = Env.Val (Num 2)) 
                    "evaluation lexical arithmetics" ;
  (* let x = 5 in if x < 4 then 42 else false 
  (In our language this is POSSIBLE) *)
  unit_test (eval_l (Let("x", 
                        Num 5, 
                        Conditional (Binop (LessThan, Var "x", Num 4),
                                    Num 42,
                                    Bool false))) 
                    (Env.empty ()) 
                    = Env.Val (Bool false))
                    "evaluation lexical conditional" ;
  (* (fun x -> x * 5) 3 *)
  unit_test (eval_l (App (Fun ("x", Binop (Times, Var "x", Num 5)),
                          Num 3))
                    (Env.empty ())
                    = Env.Val (Num 15))
                    "evaluation lexical function application" ;
  (* let rec x = fun y -> if y < 0 then y else x (y-1) in x 7 *)
  unit_test (eval_l (Letrec ("x",
                            Fun ("y", 
                                Conditional (Binop (LessThan, Var "y", Num 0),
                                            Var "y",
                                            App (Var "x", 
                                                Binop (Minus, 
                                                      Var "y", 
                                                      Num 1)))),
                            App (Var "x", Num 7)))
                    (Env.empty ())
                    = Env.Val (Num ~-1))
                    "evaluation lexical recursive function" ;
  (* let x = 5 in let f = fun y -> (x + y) in let x = 3 in f 2 *)
  unit_test (eval_l (Let ("x",
                          Num 5,
                          Let ("f",
                              Fun ("y", Binop(Plus, Var "x", Var "y")),
                              Let ("x",
                                  Num 3,
                                  App (Var "f", Num 2)))))
                    (Env.empty ())
                    = Env.Val (Num 7))
                    "evaluation lexical changing variable" ;
  ;;

let atomic_test () =
  (* 3. > 5. *)
  unit_test (eval_s (Binop(Equals, Float 3., Float 5.)) 
                    (Env.empty ())
                    = Env.Val (Bool false))
                    "atomic type extension float comparison";
  (* 3. +. 5. *)
  unit_test (eval_s (Binop(Plusf, Float 3., Float 5.)) 
                    (Env.empty ())
                    = Env.Val (Float 8.))
                    "atomic type extension float binop";
  (* "lol" = "lol" *)
  unit_test (eval_s (Binop(Equals, Str "lol", Str "lol")) 
                    (Env.empty ())
                    = Env.Val (Bool true))
                    "atomic type extension string comparison";
  (* "ab" ^ "ba" *)
  unit_test (eval_s (Binop(Concat, Str "ab", Str "ba")) 
                    (Env.empty ())
                    = Env.Val (Str "abba"))
                    "atomic type extension string concat";
  ;;

let test_all () =
  free_vars_test () ;
  subst_test () ;
  eval_s_test () ;
  eval_d_test () ;
  eval_l_test () ;
  atomic_test () ;
  Env.run_tests () ;;

let _ = test_all ()
