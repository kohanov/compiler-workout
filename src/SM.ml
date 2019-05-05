open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((ctrl, stack, ((st, input, output) as sio)) as conf) programs = match programs with
    | [] -> conf
    | BINOP op :: other -> let l :: r :: rest = stack in
      let value = Expr.eval_op op (Value.to_int r) (Value.to_int l) in
      eval env (ctrl, (Value.of_int value) :: rest, sio) other
    | CONST c :: other -> eval env (ctrl, (Value.of_int c) :: stack, sio) other
    | STRING s :: other -> eval env (ctrl, (Value.of_string s) :: stack, sio) other
    | LD s :: other -> eval env (ctrl, (State.eval st s) :: stack, sio) other
    | ST s :: other -> eval env (ctrl, tl stack, (State.update s (hd stack) st, input, output)) other
    | STA (name, len) :: other -> let (value::ids), tail = split (len + 1) stack in
      eval env (ctrl, tail, (Stmt.update st name value ids, input, output)) other
    | LABEL l :: other -> eval env conf other
    | JMP l :: _ -> eval env conf (env#labeled l)
    | CJMP (l, c) :: other -> if
        (if l = "z"
        then (Value.to_int (hd stack)) == 0
        else (Value.to_int (hd stack)) != 0)
      then eval env (ctrl, tl stack, sio) (env#labeled c)
      else eval env (ctrl, tl stack, sio) other
    | BEGIN (_, args, locals) :: other -> let f_st = State.enter st (args @ locals) in
      let f_st, f_stack = List.fold_left
        (fun (v, el :: tail) n ->  (State.update n el v, tail))
        (f_st, stack) args in
      eval env (ctrl, f_stack, (f_st, input, output)) other
    | END :: other | RET _ :: other -> (match ctrl with
      | (prg, state) :: tail -> eval env
          (tail, stack, (State.leave st state, input, output)) prg
      | _                    -> conf
    )
    | CALL (f, args_len, flag) :: other -> if env#is_label f
      then eval env ((other, st) :: ctrl, stack, sio) (env#labeled f)
      else eval env (env#builtin (ctrl, stack, sio) f args_len (not flag)) other
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) args f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

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
    | Expr.Const c -> [CONST c]
    | Expr.Array arr -> let exprs = List.flatten (List.map compile_expr (List.rev arr)) in
      exprs @ [CALL ("$array", (List.length exprs), true)]
    | Expr.String s -> [STRING s]
    | Expr.Var v -> [LD v]
    | Expr.Binop (op, left, right) -> compile_expr left @ compile_expr right @ [BINOP op]
    | Expr.Elem (el, idx) -> compile_expr idx @ compile_expr el @ [CALL ("$elem", 2, true)]
    | Expr.Length arr -> compile_expr arr @ [CALL ("$length", 1, true)]
    | Expr.Call (f, args) -> let res_args = List.concat (List.map compile_expr (List.rev args)) in
      res_args @ [CALL (f, List.length args, true)]
  in match stmt_type with
  | Stmt.Assign (s, idxs, e) -> (match idxs with
    | [] -> compile_expr e @ [ST s], false
    | _ -> let comp_idxs = List.fold_left (fun comp x -> comp @ (compile_expr x)) [] (List.rev idxs) in
      comp_idxs @ compile_expr e @ [STA (s, List.length idxs)], false)
  | Stmt.Seq (fst, snd) -> let temp_label = label#next in
    let (l, lf) = compile_impl fst temp_label in
    let (r, rf) = compile_impl snd lbl in
    l @ (if lf then [LABEL temp_label] else []) @ r, rf
  | Stmt.Skip -> [], false
  | Stmt.If (c, l, r) -> let temp_label = label#next in
    let (left, lflag) = compile_impl l lbl in
    let (right, rflag) = compile_impl r lbl in
    compile_expr c @ [CJMP ("z", temp_label)] @
    left @ check_label lflag lbl @ [LABEL temp_label] @
    right @ check_label rflag lbl, true
  | Stmt.While (c, e) -> let cond = label#next in let loop = label#next in
    let (res, _) = compile_impl e cond in
    [JMP cond; LABEL loop] @ res @ [LABEL cond] @
    compile_expr c @ [CJMP ("nz", loop)], false
  | Stmt.Repeat (e, c) -> let cond = label#next in let loop = label#next in
    let (res, _) = compile_impl e lbl in
    [LABEL loop] @ res @ [LABEL cond] @
    compile_expr c @ [CJMP ("z", loop)], false
  | Stmt.Call (f, args) -> List.concat (List.map compile_expr (List.rev args))
    @ [CALL (f, length args, false)], false
  | Stmt.Return opt -> (match opt with
    | Some value -> (compile_expr value) @ [RET true], false
    | _          -> [RET false], false
  )

let compile_stmt stmt = let lbl = label#next in
    let (result, used) = compile_impl stmt lbl in
    result @ if used then [LABEL lbl] else []

let rec compile_def f_list = List.fold_left
  (fun prev (f, (args, locals, e)) ->
    let body = compile_stmt e in
    prev @ [LABEL f] @ [BEGIN (f, args, locals)] @ body @ [END]
  ) [] f_list

let compile (f_list, stmt) =
  let stm = compile_stmt stmt in
  let def = compile_def f_list in
  stm @ [END] @ def
