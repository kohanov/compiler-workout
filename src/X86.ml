(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
(* merge_answers : instr list -> (env * instr list) -> env * instr list   *)
let merge_answers head (env, tail) = env, (head @ tail)

let zero opnd : instr = Binop ("^", opnd, opnd)

let check_binop_register op from too = match from, too with
  | R _, _ | L _, _ | _, R _ -> too, [Binop (op, from, too)]
  | _                        -> edx, [Mov (too, edx); Binop(op, from, edx)]

let cmp op l r opnd : instr list =
  let op_suffix = match op with
    | "<"  -> "l"
    | "<=" -> "le"
    | ">"  -> "g"
    | ">=" -> "ge"
    | "==" -> "e"
    | "!=" -> "ne"
    | _    -> failwith (Printf.sprintf "Unknown op %s" op)
in let _, bin_op = check_binop_register "cmp" r l
  in [zero eax] @ bin_op @ [Set (op_suffix, "%al"); Mov (eax, opnd)]

(* compile_binop : string -> env -> instr list   *)
let compile_binop op env =
  let r, l, env = env#pop2 in
  let opnd, new_env = env#allocate in
  let instr_list    = match op with
  | "+" | "-" | "*" -> let reg, bin_op = check_binop_register op r l
                       in bin_op @ [Mov (reg, opnd)]
  | "/" | "%" -> let output = if op = "/" then eax else edx
                 in [Mov (l, eax); zero edx; Cltd; IDiv r; Mov (output, opnd)]
  | "<" | "<=" | ">" | ">=" | "==" | "!=" -> (match l, r with
      | S _, S _ -> [Mov (l, edx)] @ cmp op l r opnd
      | _          -> cmp op l r opnd
  )
  | "&&" | "!!" -> [zero eax; zero edx;
                    Binop ("cmp", L 0, l); Set ("ne", "%al");
                    Binop ("cmp", L 0, r); Set ("ne", "%dl");
                    Binop (op, eax, edx); Mov (edx, opnd)]
  | _    -> failwith (Printf.sprintf "Unknown binop %s" op)
  in new_env, instr_list

let rec all_regs count = if count > 0 then all_regs (count - 1) @ [count - 1] else []

let rec compile env programs = match programs with
  | [] -> env, []
  | program::other ->
    let result_env, instr_list  = (match program with
      | BINOP op -> compile_binop op env
      | CONST c -> let operand, new_env = env#allocate
        in new_env, [Mov (L c, operand)]
      | READ -> let operand, new_env = env#allocate
        in new_env, [Call "Lread"; Mov (eax, operand)]
      | WRITE -> let operand, new_env = env#pop
        in new_env, [Push operand; Call "Lwrite"; Pop eax]
      | LD s -> let operand, new_env = (env#global s)#allocate
        in let var_name = new_env#loc s
        in new_env, [Mov (var_name, eax); Mov (eax, operand)]
      | ST s -> let operand, new_env = (env#global s)#pop
        in let var_name = new_env#loc s
        in new_env, [Mov (operand, eax); Mov (eax, var_name)]
      | LABEL l -> env, [Label l]
      | JMP l -> env, [Jmp l]
      | CJMP (l, c) -> let operand, new_env = env#pop
        in new_env, [Binop ("cmp", L 0, operand); CJmp (l, c)]
      | BEGIN (f, args, locals) -> let new_env = env#enter f args locals in
        new_env, [Push ebp; Mov (esp, ebp)]
        @ List.map (fun n -> Push (R n)) (all_regs num_of_regs)
        @ [Binop ("-", M ("$" ^ new_env#lsize), esp)]
      | END -> env, [Label env#epilogue]
        @ List.map (fun n -> Pop (R n)) (List.rev (all_regs num_of_regs))
        @ [Mov (ebp, esp); Pop ebp; Ret]
        @ [Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))]
      | CALL (f, args, flag) ->
        let pop_args = (fun (env, args) _ -> let arg, env = env#pop in (env, arg :: args)) in
        let tmp_env, new_args = List.fold_left pop_args (env, []) (all_regs args) in
        let push_cmds = List.map (fun arg -> Push arg) new_args in
        let return_block = push_cmds @ [Call f; Binop ("+", L (args * word_size), esp)] in
        if flag then let op, new_env = tmp_env#allocate in new_env, return_block @ [Mov (eax, op)]
        else tmp_env, return_block
      | RET opt -> if opt
        then let op, new_env = env#pop in new_env, [Mov (op, eax); Jmp new_env#epilogue]
        else env, [Jmp env#epilogue]
    ) in merge_answers instr_list (compile result_env other)
                                
(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (List.init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+1
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
