(* 
                         CS 51 Final Project
                         MiniML -- Evaluation
*)

(* This module implements a small untyped ML-like language under
   various operational semantics.
 *)

 open Expr ;;
  
 (* Exception for evaluator runtime, generated by a runtime error in
    the interpreter *)
 exception EvalError of string ;;
   
 (* Exception for evaluator runtime, generated by an explicit `raise`
    construct in the object language *)
 exception EvalException ;;
 
 (*......................................................................
   Environments and values 
  *)
 
 module type ENV = sig
     (* the type of environments *)
 
     (* the type of values stored in environments *)
     type env
     
     type value =
       | Val of expr
       | Closure of (expr * env)
    
     (* empty () -- Returns an empty environment *)
     val empty : unit -> env
 
     (* close expr env -- Returns a closure for `expr` and its `env` *)
     val close : expr -> env -> value
 
     (* lookup env varid -- Returns the value in the `env` for the
        `varid`, raising an `Eval_error` if not found *)
     val lookup : env -> varid -> value
 
     (* extend env varid loc -- Returns a new environment just like
        `env` except that it maps the variable `varid` to the `value`
        stored at `loc`. This allows later changing the value, an
        ability used in the evaluation of `letrec`. To make good on
        this, extending an environment needs to preserve the previous
        bindings in a physical, not just structural, way. *)
     val extend : env -> varid -> value ref -> env
 
     (* env_to_string env -- Returns a printable string representation
        of environment `env` *)
     val env_to_string : env -> string
                                  
     (* value_to_string ?printenvp value -- Returns a printable string
        representation of a value; the optional flag `printenvp`
        (default: `true`) determines whether to include the environment
        in the string representation when called on a closure *)
     val value_to_string : ?printenvp:bool -> value -> string
 
     (* for testing purposes only *)
     val run_tests : unit -> unit
   end
 
 module Env : ENV =
   struct
     type env = (varid * value ref) list
      and value =
        | Val of expr
        | Closure of (expr * env)
 
     let empty () : env = []
 
     (* duplicating the environment for closure purposes *)
     let rec fix_env (e : env) : env = 
       match e with
       | (id, id_value) :: tl -> (id, ref !id_value) :: fix_env tl
       | [] -> []
 
     let close (exp : expr) (env : env) : value =
       Closure (exp, fix_env env)
 
     let rec lookup (env : env) (varname : varid) : value =
       match env with
       | [] -> raise (EvalError (varname ^ " not found"))
       | (id, id_value) :: tail -> 
         if varname = id
         then !id_value
         else lookup tail varname
 
     (* The function can both extend or change the variable,
     it proved to be very convenient *)
 
     let rec extend (env : env) (varname : varid) (loc : value ref) : env =
       match env with
       | [] -> [varname, loc]
       | (id, old) :: tail ->
         if id = varname
         then 
           begin
             old := !loc; 
             (id, old) :: tail
           end
         else (id, old) :: extend tail varname loc
 
     let rec value_to_string ?(printenvp : bool = true) (v : value) : string =
       match v with
       | Val e -> exp_to_concrete_string e
       | Closure (expre, envir) ->
         "Closure " ^ exp_to_concrete_string expre ^
         if printenvp then ", {" ^ env_to_string envir ^ "}" else ""
 
     and env_to_string (env : env) : string =
       match env with
       | [] -> ""
       | (id, id_value) :: tail ->
         "(" ^ id ^ ": " ^ (value_to_string !id_value) ^ "); " 
         ^ (env_to_string tail)

     (* for testing purposes only *)
 
     let generate_env () : env =
       ["x", ref (Val (Num 3));
       "y", ref (Val (Num 7));
       "z", ref (Closure (Num 9, empty()))]
 
     let close_test () =
       assert (close (Num 3) (empty ()) = Closure (Num 3, empty()))
     
     let lookup_test () =
       assert (lookup (generate_env()) "y" = Val (Num 7))
 
     let extend_test () =
       let e = generate_env() in
       assert (lookup (extend e "p" (ref (Val (Num 3)))) "p" = Val (Num 3));
       assert (lookup (extend e "z" (ref (Val (Num 0)))) "z" = Val (Num 0))
 
     let value_to_string_test () =
       assert (value_to_string (Val (Bool false)) = "false")
 
     let env_to_string_test () =
       let e = generate_env () in
       assert (env_to_string e = "(x: 3); (y: 7); (z: Closure 9, {}); ")
 
     let run_tests () =
       close_test ();
       lookup_test ();
       extend_test ();
       value_to_string_test ();
       env_to_string_test ();
       ()
   end
 ;;

 (*......................................................................
   Evaluation functions
 
   Each of the evaluation functions below evaluates an expression `exp`
   in an environment `env` returning a result of type `value`. We've
   provided an initial implementation for a trivial evaluator, which
   just converts the expression unchanged to a `value` and returns it,
   along with "stub code" for three more evaluators: a substitution
   model evaluator and dynamic and lexical environment model versions.
 
   Each evaluator is of type `expr -> Env.env -> Env.value` for
   consistency, though some of the evaluators don't need an
   environment, and some will only return values that are "bare
   values" (that is, not closures). 
 
   DO NOT CHANGE THE TYPE SIGNATURES OF THESE FUNCTIONS. Compilation
   against our unit tests relies on their having these signatures. If
   you want to implement an extension whose evaluator has a different
   signature, implement it as `eval_e` below.  *)
 
 (* The TRIVIAL EVALUATOR, which leaves the expression to be evaluated
    essentially unchanged, just converted to a value for consistency
    with the signature of the evaluators. *)
    
 let eval_t (exp : expr) (_env : Env.env) : Env.value =
   (* coerce the expr, unchanged, into a value *)
   Env.Val exp ;;
 
 (* The SUBSTITUTION MODEL evaluator -- to be completed *)
 
 (* helpful functions *)
 
 let unpack_int (e : expr) : int = 
   match e with
   | Num n -> n
   | _ -> raise (EvalError "Wrong type")
   ;; 
 
 let unpack_bool (e : expr) : bool = 
   match e with
   | Bool b -> b
   | _ -> raise (EvalError "Wrong type")
   ;;
 
 let unpack_str (e : expr) : string =
   match e with
   | Str s -> s
   | _ -> raise (EvalError "Wrong type")
   ;;
 
 let unpack_float (e : expr) : float =
   match e with
   | Float f -> f
   | _ -> raise (EvalError "Wrong type")
   ;;
 
 let unval (x : Env.value) : expr = 
   match x with
   | Env.Val p -> p
   | _ -> failwith "Something went wrong (environmental syntax)"
   ;;
 
 (* universal evaluation *)
 
 let ind_eval (_exp : expr) : Env.value = 
   match _exp with
   | Num x -> Env.Val (Num x)
   | Bool b -> Env.Val (Bool b)
   | Raise -> raise (EvalError "Raise")
   | Unassigned -> raise (EvalError "Unassigned")
   | Str s -> Env.Val (Str s)
   | Float f -> Env.Val (Float f)
   | _ -> failwith "Wrong case"
   ;;
 
 (* binop expression evaluation *)
 
 let binop_match (oper : binop) (one : expr) (two : expr) : Env.value =
   match oper with
   | Plus -> Env.Val (Num (unpack_int one + unpack_int two))
   | Minus -> Env.Val (Num (unpack_int one - unpack_int two))
   | Times -> Env.Val (Num (unpack_int one * unpack_int two))
   | Equals -> Env.Val (Bool (one = two))
   | LessThan -> Env.Val (Bool (
     match one, two with
     | Num x, Num y -> x < y
     | Float x, Float y -> x < y
     | Str x, Str y -> x < y
     | _ -> raise (EvalError "Wrong types of comparison")))
   | MoreThan -> Env.Val (Bool (
    match one, two with
    | Num x, Num y -> x > y
    | Float x, Float y -> x > y
    | Str x, Str y -> x > y
    | _ -> raise (EvalError "Wrong types of comparison")))
   | Concat -> Env.Val (Str (unpack_str one ^ unpack_str two))
   | Plusf -> Env.Val (Float (unpack_float one +. unpack_float two))
   | Minusf -> Env.Val (Float (unpack_float one -. unpack_float two))
   | Timesf -> Env.Val (Float (unpack_float one *. unpack_float two))
   ;;
 
 (* unop expression evaluation *)
 let unop_match (oper : unop) (one : expr) : Env.value =
   match oper with
   | Negate -> Env.Val (Num (~- (unpack_int one)))
   | Negatef -> Env.Val (Float (~-. (unpack_float one)))
   ;;
 
 let rec eval_s (_exp : expr) (_env : Env.env) : Env.value =
   match _exp with
   | Num _
   | Bool _
   | Raise
   | Unassigned
   | Str _ 
   | Float _ -> ind_eval _exp
   | Var x -> raise (EvalError (x^" is undefined"))
   | Binop (oper, p, q) ->
     let one = eval_s p _env |> unval in
     let two = eval_s q _env |> unval in
     binop_match oper one two
   | Unop (oper, p) ->
     let one = eval_s p _env |> unval in
     unop_match oper one
   | Conditional (ife, thene, elsee) ->
     if unpack_bool (unval (eval_s ife _env))
     then eval_s thene _env
     else eval_s elsee _env
   | Fun (x, b) ->
     Env.Val (Fun (x, b))
   | Let (x, d, b) ->
     let vd = unval (eval_s d _env) in
     eval_s (subst x vd b) _env
   | Letrec (x, d, b) ->
     let vd = unval(eval_s d _env) in
     eval_s (subst x (subst x (Letrec(x, vd, Var x)) vd) b) _env
   | App (p, q) ->
     (match eval_s p _env |> unval with
     | Fun (x, b) ->
       let vq = unval (eval_s q _env) in
       eval_s (subst x vq b) _env
     | _ -> raise (EvalError "No function in the application"))
   ;;
 
 (* The DYNAMICALLY-SCOPED ENVIRONMENT MODEL evaluator -- to be
    completed *)
 
 let rec eval_d (_exp : expr) (_env : Env.env) : Env.value =
   match _exp with
   | Num _
   | Bool _
   | Raise
   | Unassigned
   | Str _ 
   | Float _ -> ind_eval _exp
   | Var x -> Env.lookup _env x
   | Binop (oper, p, q) ->
     let one = eval_d p _env |> unval in
     let two = eval_d q _env |> unval in
     binop_match oper one two
   | Unop (oper, p) ->
     let one = eval_d p _env |> unval in
     unop_match oper one
   | Conditional (ife, thene, elsee) ->
     if unpack_bool (unval (eval_d ife _env))
     then eval_d thene _env
     else eval_d elsee _env
   | Fun (x, b) ->
     Env.Val (Fun (x, b))
   | Let (x, d, b)
   | Letrec (x, d, b) ->
     let vd = eval_d d _env in
     eval_d b (Env.extend _env x (ref vd))
   | App (p, q) -> 
     (match eval_d p _env |> unval with
     | Fun (x, b) ->
       let vq = eval_d q _env in
       eval_d b (Env.extend _env x (ref vq))
     | _ -> raise (EvalError "No function in the application"))
   ;;
        
 (* The LEXICALLY-SCOPED ENVIRONMENT MODEL evaluator -- optionally
    completed as (part of) your extension *)
    
 let rec eval_l (_exp : expr) (_env : Env.env) : Env.value =
   match _exp with
   | Num _
   | Bool _
   | Raise
   | Unassigned
   | Str _ 
   | Float _ -> ind_eval _exp
   | Var x -> Env.lookup _env x
   | Binop (oper, p, q) ->
     let one = eval_l p _env |> unval in
     let two = eval_l q _env |> unval in
     binop_match oper one two
   | Unop (oper, p) ->
     let one = eval_l p _env |> unval in
     unop_match oper one
   | Conditional (ife, thene, elsee) ->
     if unpack_bool (unval (eval_l ife _env))
     then eval_l thene _env
     else eval_l elsee _env
   | Fun (x, b) ->
     Env.close (Fun (x, b)) _env
   | Let (x, d, b) ->
     let vd = eval_l d _env in
     eval_l b (Env.extend _env x (ref vd))
   | Letrec (x, d, b) ->
     let env_x = Env.extend _env x (ref (Env.Val Unassigned)) in
     let vd = eval_l d env_x in
     (match vd with
     | Env.Closure (_, new_env) ->
       eval_l b (Env.extend new_env x (ref vd))
     | _ -> raise (EvalError "Rec flag is not used"))
   | App (p, q) -> 
     (match eval_l p _env with
     | Env.Closure (Fun(x,b), closed_env) ->
       let vq = eval_l q _env in
       eval_l b (Env.extend closed_env x (ref vq))
     | _ -> raise (EvalError "No function in the application"))
   ;;

 (* Connecting the evaluators to the external world. The REPL in
    `miniml.ml` uses a call to the single function `evaluate` defined
    here. Initially, `evaluate` is the trivial evaluator `eval_t`. But
    you can define it to use any of the other evaluators as you proceed
    to implement them. (We will directly unit test the four evaluators
    above, not the `evaluate` function, so it doesn't matter how it's
    set when you submit your solution.) *)
    
 let evaluate = eval_l ;;
 