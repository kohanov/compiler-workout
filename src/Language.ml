(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
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

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env cfg st_type =
      let (st, input, output) = cfg in
      match st_type with
      | Read r                      -> (State.update r (hd input) st, tl input, output)
      | Write expr                  -> (st, input, output @ [Expr.eval st expr])
      | Assign (name, expr)         -> (State.update name (Expr.eval st expr) st, input, output)
      | Seq (first_type, last_type) -> eval env (eval env cfg first_type) last_type
      | Skip                        -> cfg
      | If (expr, l, r)             -> let cond = (Expr.eval st expr) != 0
                                       in eval env cfg (if cond then l else r)
      | While (cond, expr)          -> if (Expr.eval st cond) != 0
                                       then eval env (eval env cfg expr) st_type
                                       else (st, input, output)
      | Repeat (expr, cond)         -> let (s, i, o) = eval env cfg expr in
                                       if (Expr.eval s cond) = 0
                                       then eval env (s, i, o) st_type
                                       else (s, i, o)
      | Call (f, args)              -> let (names, locals, e) = env#definition f
                                       in let values = List.map (Expr.eval st) args
                                       in let n2v = List.combine names values
                                       in let f_st = State.push_scope st (names @ locals)
                                       in let f_st = List.fold_left (fun x (n, v) -> State.update n v x) f_st n2v
                                       in let st2, i2, o2 = eval env (f_st, input, output) e
                                       in State.drop_scope st2 st, i2, o2
    (* Statement parser *)
    ostap (                                      
      if_tail: 
          "fi" {Skip}
        | "else" r: parse "fi" {r}
        | "elif" e: !(Expr.parse) "then" l: parse r: if_tail {If (e, l, r)}
      ;
      stmt: 
          "read" "(" s: IDENT ")" {Read s}
        | "write" "(" e: !(Expr.parse) ")" {Write e}
        | s:IDENT ":=" e: !(Expr.parse) {Assign (s, e)}
        | "skip" {Skip}
        | "if" e: !(Expr.parse) "then" l: parse r: if_tail {If (e, l ,r)}
        | "while" cond: !(Expr.parse) "do" body: parse "od" {While (cond, body)}
        | "repeat" body: parse "until" cond: !(Expr.parse) {Repeat (body, cond)}
        | "for" i: parse "," cond: !(Expr.parse) "," it: parse
          "do" body: parse "od" {Seq (i, While(cond, Seq(body, it)))}
        | f: IDENT "(" args: (!(Expr.parse))* ")" {Call (f, args)}
      ;
      parse: x: stmt ";" xs: parse {Seq (x, xs)} | stmt
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      parse: 
        "fun" f: IDENT "(" args: (IDENT)* ")"
        locals: (%"local" (IDENT)* )? "{"
          body: !(Stmt.parse)
        "}"
        {
          let locals = match locals with
          | Some x -> x
          | _ -> []
          in f, (args, locals, body)
        }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
