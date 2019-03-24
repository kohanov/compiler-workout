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
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* application *)
let ($) f x = f x

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval envr cfg programs =
    let (stack, (st, input, output)) = cfg in match programs with
    | []               -> cfg
    | BINOP op    :: o -> let value = Expr.eval_op op (hd $ tl stack) (hd stack) in
                          eval envr (value :: (tl $ tl stack), (st, input, output)) o
    | CONST c     :: o -> eval envr (c :: stack, (st, input, output)) o
    | READ        :: o -> eval envr (hd input :: stack, (st, tl input, output)) o
    | WRITE       :: o -> eval envr (tl stack, (st, input, output @ [hd stack])) o
    | LD s        :: o -> eval envr (st s :: stack, (st, input, output)) o
    | ST s        :: o -> eval envr (tl stack, (Expr.update s (hd stack) st, input, output)) o
    | LABEL l     :: o -> eval envr cfg o
    | JMP l       :: _ -> eval envr cfg (envr#labeled l)
    | CJMP (l, c) :: o -> if (if l = "z" then (hd stack) == 0 else (hd stack) != 0)
                          then eval envr (tl stack, (st, input, output)) (envr#labeled c)
                          else eval envr (tl stack, (st, input, output)) o
    ;;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

(* Helper class for generating distinct labels  *)
let label =
  object(self)
    val mutable v = 0
    method next : string = let res = "label"^(string_of_int v) in v <- v + 1; res
  end

let check_label cond lbl = if cond then [] else [JMP lbl]

(* val compile_impl : Stmt.t -> string -> (prg, bool) *)
let rec compile_impl stmt_type lbl : prg * bool =
    let rec compile_expr e = match e with
        | Expr.Const c                 -> [CONST c]
        | Expr.Var v                   -> [LD v]
        | Expr.Binop (op, left, right) -> compile_expr left @ compile_expr right @ [BINOP op]
    in match stmt_type with
    | Stmt.Read s         -> [READ; ST s], false
    | Stmt.Write e        -> compile_expr e @ [WRITE], false
    | Stmt.Assign (s, e)  -> compile_expr e @ [ST s], false
    | Stmt.Seq (fst, snd) -> let temp_label = label#next in
                             let (l, lf) = compile_impl fst temp_label in
                             let (r, rf) = compile_impl snd lbl in
                             l @ (if lf then [LABEL temp_label] else []) @ r, rf
    | Stmt.Skip           -> [], false
    | Stmt.If (c, l, r)   -> let temp_label = label#next in
                             let (left, lflag) = compile_impl l lbl in
                             let (right, rflag) = compile_impl r lbl in
                             compile_expr c @ [CJMP ("z", temp_label)] @
                             left @ check_label lflag lbl @ [LABEL temp_label] @
                             right @ check_label rflag lbl, true
    | Stmt.While (c, e)   -> let cond = label#next in let loop = label#next in
                             let (res, _) = compile_impl e cond in
                             [JMP cond; LABEL loop] @ res @ [LABEL cond] @
                             compile_expr c @ [CJMP ("nz", loop)], false
    | Stmt.DoWhile (c, e) -> let cond = label#next in let loop = label#next in
                             let (res, _) = compile_impl e lbl in
                             [LABEL loop] @ res @ [LABEL cond] @
                             compile_expr c @ [CJMP ("z", loop)], false
                             ;;

let compile t = let lbl = label#next in
    let (result, used) = compile_impl t lbl in
    result @ if used then [LABEL lbl] else [];;