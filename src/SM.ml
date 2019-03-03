open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* application *)
let ($) f x = f x

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval cfg programs =
    let eval_one (stack, (st, input, output)) p = match p with
        | BINOP op -> ((Expr.eval_op op (hd $ tl stack) (hd stack)) :: (tl $ tl stack), (st, input, output))
        | CONST c  -> (c :: stack, (st, input, output))
        | READ     -> (hd input :: stack, (st, tl input, output))
        | WRITE    -> (tl stack, (st, input, output @ [hd stack]))
        | LD s     -> (st s :: stack, (st, input, output))
        | ST s     -> (tl stack, (Expr.update s (hd stack) st, input, output))
    in match programs with
    | [] -> cfg
    | program :: other -> eval (eval_one cfg program) other;;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt_type =
    let rec compile_expr e = match e with
        | Expr.Const c                 -> [CONST c]
        | Expr.Var v                   -> [LD v]
        | Expr.Binop (op, left, right) -> compile_expr left @ compile_expr right @ [BINOP op]
    in match stmt_type with
    | Stmt.Read s         -> [READ; ST s]
    | Stmt.Write e        -> compile_expr e @ [WRITE]
    | Stmt.Assign (s, e)  -> compile_expr e @ [ST s]
    | Stmt.Seq (fst, snd) -> compile fst @ compile snd;;
