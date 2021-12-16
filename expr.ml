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
  | Var v -> SS.singleton v
  | Num _ | Bool _ | Raise | Unassigned -> SS.empty
  | Unop (_, e) -> free_vars e
  | Binop (_, e1, e2)
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) -> SS.union (SS.union (free_vars e1) (free_vars e2)) (free_vars e3)
  | Fun (v, e) -> SS.remove v (free_vars e)
  | Let (v, e1, e2) -> SS.union (SS.remove v (free_vars e2)) (free_vars e1)
  | Letrec (v, e1, e2) -> SS.union (SS.remove v (free_vars e1)) (SS.remove v (free_vars e2))
   ;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)
let new_varname : unit -> varid =
  let suffix = ref ~-1 in 
  fun () -> suffix := !suffix + 1;
    "var" ^ string_of_int !suffix ;;

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
  | Var v -> if v = var_name then repl else exp
  | Num _ | Bool _ | Raise | Unassigned -> exp
  | Unop (u, e) -> Unop (u, subst var_name repl e)
  | Binop (b, e1, e2) -> Binop (b, subst var_name repl e1, subst var_name repl e2)
  | Conditional (e1, e2, e3) -> Conditional (subst var_name repl e1,
                                            subst var_name repl e2, 
                                            subst var_name repl e3)
  | Fun (v, e) -> if v = var_name then exp
                  else if SS.mem v (free_vars repl) then
                    let x = new_varname () in 
                    Fun (x, subst var_name repl (subst v (Var x) e))
                  else 
                    Fun (v, subst var_name repl e)
  | Let (v, e1, e2) -> if v = var_name then Let (v, subst var_name repl e1, e2)
                       else if SS.mem v (free_vars repl) then 
                         let x = new_varname () in 
                         Let (x, subst var_name repl e1, subst var_name repl (subst v (Var x) e2))
                       else 
                         Let (v, subst var_name repl e1, subst var_name repl e2)
  | Letrec (v, e1, e2) -> if v = var_name then exp
                          else if SS.mem v (free_vars repl) then 
                            let x = new_varname () in 
                            Letrec (x, subst var_name repl (subst v (Var x) e1), 
                                    subst var_name repl (subst v (Var x) e2))
                          else
                            Letrec (v, subst var_name repl e1, subst var_name repl e2)
  | App (e1, e2) -> App (subst var_name repl e1, subst var_name repl e2)
  ;;
     
(*......................................................................
  String representations of expressions
 *)

(* helper functions to convert unop and binops into concrete or abstract strings *)   
let unop_string (u: unop) (con: bool) : string =
  match u with 
  | Negate -> if con then "~-" else "Unop(Negate, "
  ;;

let binop_string (b: binop) (con: bool) : string = 
  match b with
  | Plus -> if con then " + " else "Binop(Plus, "
  | Minus -> if con then " - " else "Binop(Minus, "
  | Times -> if con then " * " else "Binop(Times, "
  | Equals -> if con then " = " else "Binop(Equals, "
  | LessThan -> if con then " < " else "Binop(LessThan, "
  ;;
 
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var v -> v
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unop (u, e) -> unop_string u true ^ exp_to_concrete_string e
  | Binop (b, e1, e2) -> exp_to_concrete_string e1 ^ binop_string b true ^ exp_to_concrete_string e2
  | Conditional (e1, e2, e3) -> "if " ^ exp_to_concrete_string e1 ^
                                " then " ^  exp_to_concrete_string e2 ^
                                " else " ^ exp_to_concrete_string e3
  | Fun (v, e) -> "fun " ^ v ^ " -> "  ^ exp_to_concrete_string e
  | Let (v, e1, e2) -> "let " ^ v ^ " = " ^ exp_to_concrete_string e1 ^ " in " ^
                        exp_to_concrete_string e2
  | Letrec (v, e1, e2) -> "let rec " ^ v ^ " = " ^ exp_to_concrete_string e1 ^ " in " ^
                           exp_to_concrete_string e2
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> exp_to_concrete_string e1 ^ " " ^ exp_to_concrete_string e2
  ;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var(" ^ v ^ ")"
  | Num n -> "Num(" ^ string_of_int n ^ ")"
  | Bool b -> "Bool(" ^ string_of_bool b ^ ")"
  | Unop (u, e) -> unop_string u false ^ exp_to_abstract_string e ^ ")"
  | Binop (b, e1, e2) -> binop_string b false^ exp_to_abstract_string e1 ^
                         ", " ^ exp_to_abstract_string e2 ^ ")"
  | Conditional (e1, e2, e3) -> "Conditional(" ^ exp_to_abstract_string e1 ^
                                ", " ^ exp_to_abstract_string e2 ^ ", " ^
                                exp_to_abstract_string e3 ^ ")"
  | Fun (v, e) -> "Fun(" ^ v ^ ", " ^ exp_to_abstract_string e ^ ")"
  | Let (v, e1, e2) -> "Let(" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^
                        exp_to_abstract_string e2 ^ ")"
  | Letrec (v, e1, e2) -> "Letrec(" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^
                          exp_to_abstract_string e2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> "App(" ^ exp_to_abstract_string e1 ^ ", " ^
                    exp_to_abstract_string e2 ^ ")"
   ;;
