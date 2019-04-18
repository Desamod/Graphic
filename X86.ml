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


let compile_binop op loc_x loc_y loc_r =
  let y2a_compute_send comp = [Mov (loc_y, eax)] @ comp @ [Mov (eax, loc_r)] in
  let compareyx_single_send flag = [Mov (loc_y, eax); Binop ("-", loc_x, eax);
                                    Mov (L 0, eax); Set (flag, "%al"); Mov (eax, loc_r)] in
  let compareyx_double_send flag1 flag2 joiner = [Mov (loc_y, eax); Binop ("-", loc_x, eax); Mov (eax, loc_r);
                                                  Mov (L 0, eax); Mov (L 0, edx); Set (flag1, "%al"); Set (flag2, "%dl"); 
                                                  Binop (joiner, edx, eax); Mov (eax, loc_r)] in
  let logicop_send op =
    let signum arg = [Push ebp; Mov (arg, ebp); Binop ("!!", ebp, ebp); Pop ebp]
    in [Mov (L 0, eax); Mov (L 0, edx)]
       @ signum loc_x @ [Set ("nz", "%dl")] @ signum loc_y
       @ [ Set ("nz", "%al"); Binop (op, edx, eax); Mov (eax, loc_r)]
  in match op with
     | "+" -> y2a_compute_send [Binop ("+", loc_x, eax)]
     | "-" -> y2a_compute_send [Binop ("-", loc_x, eax)]
     | "*" -> y2a_compute_send [Binop ("*", loc_x, eax)]
     | "/" -> y2a_compute_send [Cltd; IDiv loc_x]
     | "%" -> y2a_compute_send [Cltd; IDiv loc_x; Mov (edx, eax)]

     | "==" -> compareyx_single_send "z"
     | "!=" -> compareyx_single_send "nz"
     | "<=" -> compareyx_double_send "z" "s" "!!"
     | "<" -> compareyx_single_send "s"
     | ">=" -> compareyx_double_send "z" "ns" "!!"
     | ">" -> compareyx_double_send "nz" "ns" "&&"

     | "!!" -> logicop_send "!!"
     | "&&" -> logicop_send "&&"

let compile_instr env instr =
  let force_reg_mov loc_from loc_to = match loc_from, loc_to with
    | R _ , _
    | L _, _
    | _ , R _
    | _, L _ -> [Mov (loc_from, loc_to)]
    | _, _ -> [Mov (loc_from, eax); Mov (eax, loc_to)]
  in match instr with
     | CONST n -> let loc, env' = env#allocate in env', [Mov (L n, loc)]
     (* | WRITE -> let loc, env' = env#pop in
      *            env', [Push loc; Call "Lwrite"; Binop ("+", L 4, esp)]
      * | READ -> let loc, env' = env#allocate in
      *           env', [Call "Lread"; Mov (eax, loc)] *)
     | ST var -> let env' = env#global var in
                 let loc, env'' = env'#pop in
                 env'', force_reg_mov loc (env''#loc var)
     | LD var -> let env' = env#global var in
                 let loc, env'' = env'#allocate in
                 env'', force_reg_mov (env''#loc var) loc
     | BINOP op -> let loc_x, loc_y, env' = env#pop2 in
                   let loc_r, env'' = env'#allocate in
                   env'', compile_binop op loc_x loc_y loc_r
     | LABEL label -> env, [Label label]
     | JMP label -> env, [Jmp label]
     | CJMP (mode, label) ->
        let loc_arg, env' = env#pop in
        let loc_res, env'' = env'#allocate in
        (* Force evaluate stack top because expression may not include computations at all *)
        let force_compute = compile_binop "!!" loc_arg loc_arg loc_res in
        env'', force_compute @ [CJmp (mode, label)]
     | RET (opt_return) ->
        let end_jmp = Jmp (env#epilogue)
        in (if (opt_return)
            then (let loc, env' = env#pop
                  in env', [Mov (loc, eax); end_jmp])
            else env, [end_jmp])
     | BEGIN (name, args, locals) ->
        let env' = env#enter name args locals in
        let locals_allocation = Binop ("-", M ("$" ^ env'#lsize), esp) in
        let prologue = [Push ebp; Mov (esp, ebp); locals_allocation] in
        env', prologue
     | END ->
        (* runs after main program, so no need to restore env by 'leave' *)
        let epilogue = [Mov (ebp, esp); Pop ebp] in
        let const_setup = (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size)) in
        env, [Label env#epilogue] @ epilogue @ [Ret; Meta const_setup]
     | CALL (name, args_amount, returns_value) ->
        let name = match name with
          | "write" -> "Lwrite"
          | "read" -> "Lread"
          | _ -> name in
        let save_registers, restore_registers =
          let reg_ops reg = Push reg, Pop reg in
          let op_pairs = List.map reg_ops env#live_registers in
          let forward, backward' = List.split op_pairs in
          forward, List.rev backward' in
        let env, _, symbolic2hardware =
          let rec place_args env' rem_amount pushes = match rem_amount with
            | 0 -> env', 0, pushes
            | _ -> let pop_from, env'' = env'#pop in
                   place_args env'' (rem_amount-1) ((Push pop_from)::pushes)
          in place_args env args_amount [] in
        (* call *)
        let restore_stack = [Binop ("+", L (args_amount * word_size), esp)] in
        let env, hardware2symbolic =
          if returns_value
          then let push_to, env' = env#allocate in env', [Mov (eax, push_to)]
          else env, []
        in env, save_registers @ symbolic2hardware @ [Call name]
                @ restore_stack @ restore_registers @ hardware2symbolic
       
(* let compile env code =
 *   let suffix = function
 *   | "<"  -> "l"
 *   | "<=" -> "le"
 *   | "==" -> "e"
 *   | "!=" -> "ne"
 *   | ">=" -> "ge"
 *   | ">"  -> "g"
 *   | _    -> failwith "unknown operator"	
 *   in
 *   let rec compile' env scode = failwith "Not implemented" in
 *   compile' env code *)
                                                        

let rec compile env program = match program with
  (* | [] -> env, [Comment] *)
  | [] -> env, []
  | cmd::program' -> let (env', cmd_compiled) = compile_instr env cmd in
                     let (env'', program_compiled) = compile env' program' in
                     env'', [] @ cmd_compiled  @ program_compiled


(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
(* let make_assoc l = List.combine l (List.init (List.length l) (fun x -> x)) *)
let rec buildList i n = let x = i+1 in if i <= n then i::(buildList x n) else []
let make_assoc l = List.combine l (buildList 0 ((List.length l) - 1))


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
        | []                            -> R 0     , 0
        | (S n)::_                      -> S (n+1) , n+2
        | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
        | _                             -> let n = List.length locals in S n, n+1
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