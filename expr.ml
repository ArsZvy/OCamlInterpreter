(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

 type unop =
  | Negate
  | Negatef
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
  | MoreThan
  | Concat
  | Plusf
  | Minusf
  | Timesf
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
  | Str of string                        (* strings *)
  | Float of float                       (* float *)
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

let unop_convert_con (u : unop) : string =
  match u with
  | Negate -> "~-"
  | Negatef -> "~-."
  ;;

let unop_convert_abs (u : unop) : string =
  match u with
  | Negate -> "Negate"
  | Negatef -> "Negatef"
  ;;

let binop_convert_con (b : binop) : string =
  match b with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Equals -> "="
  | LessThan -> "<"
  | MoreThan -> ">"
  | Concat -> "^"
  | Plusf -> "+."
  | Minusf -> "-."
  | Timesf -> "*."
  ;;

let binop_convert_abs (b : binop) : string =
  match b with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Equals -> "Equals"
  | LessThan -> "LessThan"
  | MoreThan -> "MoreThan"
  | Concat -> "Concat"
  | Plusf -> "Plusf"
  | Minusf -> "Minusf"
  | Timesf -> "Timesf"
  ;;

(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)

let rec exp_to_concrete_string (e : expr) : string = 
  match e with
    | Var v -> v
    | Num x -> string_of_int x
    | Bool b -> string_of_bool b
    | Unop (u, ex) -> 
      unop_convert_con u ^ exp_to_concrete_string ex
    | Binop (b, ex1, ex2) ->
      exp_to_concrete_string ex1 ^ binop_convert_con b
      ^ exp_to_concrete_string ex2
    | Conditional (ife, thene, elsee) ->
      "if " ^ exp_to_concrete_string ife ^
      " then " ^ exp_to_concrete_string thene ^
      " else " ^ exp_to_concrete_string elsee
    | Fun (v, ex) ->
      "fun " ^ v ^ " -> " ^ exp_to_concrete_string ex
    | Let (v, ex1, ex2) ->
      "let " ^ v ^ " = " ^ exp_to_concrete_string ex1 ^
      " in " ^ exp_to_concrete_string ex2
    | Letrec (v, ex1, ex2) ->
      "let rec " ^ v ^ " = " ^ exp_to_concrete_string ex1 ^
      " in " ^ exp_to_concrete_string ex2
    | Raise -> "raise"
    | Unassigned -> "none"
    | App (ex1, ex2) ->
      "(" ^ exp_to_concrete_string ex1 ^ ") (" ^
      exp_to_concrete_string ex2 ^ ")"
    | Str s -> "\"" ^ s ^ "\""
    | Float f -> string_of_float f
  ;;

(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)

let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x -> SS.add x SS.empty
  | Num _
  | Bool _
  | Raise
  | Str _
  | Float _
  | Unassigned -> SS.empty
  | Unop (_, e) -> free_vars e
  | Binop (_, p, q)
  | App (p, q) -> SS.union (free_vars p) (free_vars q)
  | Conditional (ife, thene, elsee)
    -> SS.union (SS.union (free_vars ife) (free_vars thene)) (free_vars elsee)
  | Fun (x, p) -> SS.remove x (free_vars p)
  | Let (x, p, q) 
    -> SS.union (SS.remove x (free_vars q)) (free_vars p)
  | Letrec (x, p, q)
    -> SS.remove x (SS.union (free_vars q) (free_vars p))
  ;;

(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)

let new_varname =
  let num = ref 0 in
  fun () ->
    num := !num + 1;
    "var" ^ string_of_int !num
  ;;

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
    if x = var_name
    then repl
    else exp
  | Num _
  | Bool _
  | Str _
  | Float _ -> exp
  | Unop (u, e) -> Unop (u, subst var_name repl e)
  | Binop (b, e1, e2) -> 
    Binop (b, subst var_name repl e1, subst var_name repl e2)
  | Conditional (ife, thene, elsee) ->
    Conditional (subst var_name repl ife, 
                subst var_name repl thene, 
                subst var_name repl elsee)
  | Fun (v, q) -> 
    if v = var_name
    then Fun (v, q)
    else
      if SS.mem v (free_vars repl)
      then 
        let z = new_varname () in
        Fun (z, subst var_name repl (subst v (Var z) q))
      else Fun (v, subst var_name repl q)
  | Let (v, q, r) -> 
    if v = var_name 
    then Let (v, subst v repl q, r)
    else
      if SS.mem v (free_vars repl)
      then
        let z = new_varname () in
        Let (z, subst var_name repl q, 
                subst var_name repl (subst v (Var z) r))
      else
        Let (v, subst var_name repl q, subst var_name repl r)
  | Letrec (v, q, r) -> 
    if v = var_name 
    then Letrec (v, q, r)
    else
      if SS.mem v (free_vars repl)
      then
        let z = new_varname () in
        Letrec (z, subst var_name repl (subst v (Var z) q), 
                  subst var_name repl (subst v (Var z) r))
      else
        Letrec (v, subst var_name repl q, subst var_name repl r)
  | Raise -> Raise
  | Unassigned -> Unassigned
  | App (q, r) ->
    App (subst var_name repl q, subst var_name repl r)
  ;;

(*......................................................................
  String representations of expressions
 *)

(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var " ^ v
  | Num x -> "Num " ^ string_of_int x
  | Bool b -> "Bool " ^ string_of_bool b
  | Unop (u, ex) -> 
    "Unop (" ^ unop_convert_abs u ^ ", " ^ exp_to_abstract_string ex ^ ")"
  | Binop (b, ex1, ex2) ->
    "Binop (" ^ binop_convert_abs b ^ ", " ^
    exp_to_abstract_string ex1 ^ ", " ^
    exp_to_abstract_string ex2 ^ ")"
  | Conditional (ife, thene, elsee) ->
    "Conditional (" ^ 
    exp_to_abstract_string ife ^ ", " ^
    exp_to_abstract_string thene ^ ", " ^
    exp_to_abstract_string elsee ^ ")"
  | Fun (v, ex) ->
    "Fun (" ^ v ^ ", " ^ exp_to_abstract_string ex ^ ")"
  | Let (v, ex1, ex2) ->
    "Let (" ^ v ^ ", " ^ exp_to_abstract_string ex1 ^
    ", " ^ exp_to_abstract_string ex2 ^ ")"
  | Letrec (v, ex1, ex2) ->
    "Letrec (" ^ v ^ ", " ^ exp_to_abstract_string ex1 ^
    ", " ^ exp_to_abstract_string ex2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (ex1, ex2) ->
    "App (" ^ exp_to_abstract_string ex1 ^ ", " ^
    exp_to_abstract_string ex2 ^ ")"
  | Str s -> "Str (\"" ^ s ^ "\")"
  | Float f -> "Float (" ^ string_of_float f ^ ")"
;;
