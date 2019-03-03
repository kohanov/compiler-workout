(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let to_bool e = e != 0

    let from_bool e = if e then 1 else 0

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let eval_op op l r = match op with
        | "+"  -> l + r
        | "-"  -> l - r
        | "*"  -> l * r
        | "/"  -> l / r
        | "%"  -> l mod r
        | "<"  -> from_bool(l < r)
        | "<=" -> from_bool(l <= r)
        | ">"  -> from_bool(l > r)
        | ">=" -> from_bool(l >= r)
        | "==" -> from_bool(l = r)
        | "!=" -> from_bool(l != r)
        | "&&" -> from_bool(to_bool l && to_bool r)
        | "!!" -> from_bool(to_bool l || to_bool r)
        | _    -> failwith (Printf.sprintf "Unsupported operator %s" op)

    let rec eval s expr = match expr with
        | Const c -> c
        | Var v -> s v
        | Binop (op, left, right) ->
            let l = eval s left in
            let r = eval s right in
            eval_op op l r

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
    )

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (st, input, output) st_type = match st_type with
        | Read r                      -> (Expr.update r (List.hd input) st, List.tl input, output)
        | Write expr                  -> (st, input, output @ [Expr.eval st expr])
        | Assign (name, expr)         -> (Expr.update name (Expr.eval st expr) st, input, output)
        | Seq (first_type, last_type) -> eval (eval (st, input, output) first_type) last_type;;

    (* Statement parser *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
