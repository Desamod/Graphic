open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
          
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
  eval env (
    match insn with
    | BINOP op -> 
      let y::x::stack' = stack in (cstack, Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack', c)
    | CONST i -> 
      (cstack, (Value.of_int i)::stack, c)
    | STRING s -> 
      (cstack, (Value.of_string s)::stack, c)
    | SEXP (s, i) ->
      let (xs, stack') = split i stack in
      cstack, (Value.sexp s (List.rev xs))::stack', c
    | LD x -> 
      (cstack, (State.eval st x) :: stack, c)
    | ST x -> 
      let z::stack' = stack in (cstack, stack', (State.update x z st, i, o))
    | STA (x, n) -> 
      let (z::args, stack') = split (n + 1) stack
      in (cstack, stack', (Stmt.update st x z (List.rev args), i, o))
    | LABEL _ -> 
      conf
    | JMP _ -> 
      conf
    | CJMP (cond, l) -> 
      let z::stack' = stack in (cstack, stack', c)
    | BEGIN (_, args, ls) -> 
      let inner_st = State.enter st (args @ ls) in 
      let st', stack' = List.fold_left (fun (s, (z :: stck)) x -> State.update x z s, stck) (inner_st, stack) args in
      (cstack, stack', (st', i, o))
    | END | RET _    ->
      (match cstack with 
      | [] -> conf
      | (_, s) :: cstack' -> (cstack', stack, (State.leave st s, i, o)) 
      )
    | CALL (name, argc, p) -> 
      if env#is_label name
      then ((prg', st)::cstack, stack, c)
      else (env#builtin conf name argc p)
    | DROP ->
      let z::stack' = stack in (cstack, stack', c)
    | DUP ->
      let z::stack' = stack in (cstack, z::z::stack', c)
    | SWAP ->
      let x::y::stack' = stack in (cstack, y::x::stack', c)
    | TAG s ->
      let z::stack' = stack in (cstack, (match z with
        | Value.Sexp (s', _) when s = s' -> Value.of_int 1
        | _ -> Value.of_int 0)::stack', c)
    | ENTER ss ->
      let (xs, stack') = split (List.length ss) stack in
      let st' = List.fold_left2 (fun s x v -> State.bind x v s) State.undefined ss xs in
      cstack, stack', (State.push st st' ss, i, o)
    | LEAVE ->
      cstack, stack, (State.drop st, i, o)
  )
   (let cjmp_cond cond x =
      match cond with
      | "z"  -> x = 0
      | "nz" -> x <> 0
      | _    -> failwith "Unexpected cjump parameter"
    in
      match insn with
      | JMP l             -> env#labeled l
      | CJMP (cond, l)    -> let z::stack' = stack in (if cjmp_cond cond (Value.to_int z) then (env#labeled l) else prg')
      | CALL (name, _, _) -> if env#is_label name then env#labeled name else prg'
      | END | RET _       -> (match cstack with [] -> [] | (p, _) :: _ -> p)
      | _                 -> prg'
   )


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
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
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
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
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse p = (
    let rec compile = function
    | Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident _  -> [DROP]
    | Stmt.Pattern.Sexp (s, xs) -> (
      let res, _ = List.fold_left
        (fun (acc, pos) p -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ compile p, pos + 1))
        ([], 0) xs in
      [DUP; TAG s; CJMP ("z", lfalse)] @ res
    ) in compile p
  )
  and bindings p = (
    let rec bind = (function
    | Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident _ -> [SWAP]
    | Stmt.Pattern.Sexp (_, xs) ->
      let res, _ = List.fold_left
        (fun (acc, pos) p -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind p, pos + 1))
        ([], 0) xs
      in res @ [DROP]
    ) in bind p @ [ENTER (Stmt.Pattern.vars p)]
  )
  and expr = (function
    | Expr.Const n          -> [CONST n]
    | Expr.Array es         -> call ".array" es false
    | Expr.Sexp (s, xs)     -> exprList xs @ [SEXP (s, List.length xs)]
    | Expr.String s         -> [STRING s]
    | Expr.Var x            -> [LD x]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
    | Expr.Elem (b, j)      -> call ".elem" [b; j] false
    | Expr.Length v         -> call ".length" [v] false
    | Expr.Call (f, es)     -> call f (List.rev es) false
  ) 
  and exprList es = List.flatten (List.map expr es) in
  let rec compile_stmt l env = (function
    | Stmt.Assign (x, [], e) -> 
        env, false, expr e @ [ST x]
    | Stmt.Assign (x, ks, e) -> 
        env, false, exprList (ks @ [e]) @ [STA (x, List.length ks)]
    | Stmt.Seq (s1, s2) -> 
        let env, _, compiled_s1 = compile_stmt l env s1 in
        let env, _, compiled_s2 = compile_stmt l env s2 in
        env, false, compiled_s1 @ compiled_s2  
    | Stmt.Skip -> 
        env, false, []
    | Stmt.If (c, s, es) -> 
        let else_label, env = env#get_label in
        let endif_label, env = env#get_label in
        let env, _, compiled_s = compile_stmt l env s in
        let env, _, compiled_es = compile_stmt l env es in
        env, false, 
        expr c @ [CJMP("z", else_label)] @ compiled_s @ [JMP endif_label; LABEL else_label] 
          @ compiled_es @ [LABEL endif_label]
    | Stmt.While (c, s)  ->
        let while_label, env = env#get_label in
        let endwhile_label, env = env#get_label in 
        let env, _, compiled_s = compile_stmt l env s in
        env, false,
        [LABEL while_label] @ expr c @ [CJMP("z", endwhile_label)]
        @ compiled_s @ [JMP while_label; LABEL endwhile_label]
    | Stmt.Repeat (s, c) ->
        let repeat_label, env = env#get_label in
        let env, _, compiled_s = compile_stmt l env s in
        env, false,
        [LABEL repeat_label] @ compiled_s @ (expr c) @ [CJMP("z", repeat_label)]
    | Stmt.Call (name, args) ->
        env, false, call name args true
    | Stmt.Return optexpr ->
        env, false, 
          (match optexpr with Some e -> expr e | None -> []) @
          [RET (match optexpr with Some _ -> true | None -> false)]
    | Stmt.Leave ->
        env, false, [LEAVE]
    | Stmt.Case (ex, ps) ->
        let rec compilePat env l fst lend = (function 
          | [] -> env, []
          | (p, e)::ps' ->
            let env, _, compiled_e = compile_stmt l env e in
            let lfalse, env = env#get_label in
            let start = if fst then [] else [LABEL l] in
            let env, compiled_p = compilePat env lfalse false lend ps' in
            env, start @ (pattern lfalse p) @ bindings p @ compiled_e @ [LEAVE; JMP lend] @ compiled_p
        ) in
        let lend, env = env#get_label in
        let env, compiled_pat = compilePat env "" true lend ps in
        env, false, expr ex @ compiled_pat @ [LABEL lend  ]
  ) in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

