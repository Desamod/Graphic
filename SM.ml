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
(* comment                  *)        | COMMENT of string
(*  *)                                | CZCLEARJMP of string * int
with show


let i2s = GT.transform(insn) (new @insn[show]) ()
let print_prg p = List.iter (fun i -> Printf.eprintf "%s\n" (show(insn) i)) p
                            
       
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
          
let rec eval env (cs, (ds:Value.t list), (state, inp, out, (foo: Value.t option) as subconf) as config2) program =
  let rec eval_cmd config command = match config, command with
    | (_, y::x::rest, _), BINOP (str_op)
      -> let result=Value.of_int (Expr.to_func str_op (Value.to_int x) (Value.to_int y))
         in (cs, result::rest, subconf)

    | _, COMMENT _ -> (cs, ds, subconf)
    | _, CONST value -> (cs, (Value.of_int value)::ds, subconf)
    | _, STRING str -> (cs, (Value.of_string (Bytes.of_string str))::ds, subconf)
    | _, SEXP (name, size) ->
       let (values, ds') = split size ds in
       let value = Value.Sexp (name, values) in
       (cs, value::ds', subconf)
    | _, DROP -> let _::ds' = ds in (cs, ds', subconf)
    | _, DUP -> let top::_ = ds in (cs, top::ds, subconf)
    | _, SWAP -> let x::y::ds' = ds in (cs, y::x::ds', subconf)
    | _, TAG (name) ->
       let top::ds' = ds in
       let value = match top with
         | Value.Sexp (name', _) -> Value.of_int (if name=name' then 1 else 0)
         | _ -> Value.of_int 0 in
       (cs, value::ds', subconf)
    | _, LD (var) -> (cs, (State.eval state var)::ds, subconf)
    | (_, value::rest, _), ST (var) -> (cs, rest, (State.update var value state, inp, out, foo))
    | (_, _, _), STA (var, inds_amount) -> (* ia stack tops are indices, next is value *)
       let (indices, value::ds') = split inds_amount ds in
       let state' = Stmt.update state var value indices in
       (cs, ds', (state', inp, out, foo))
    | _, LABEL _ -> config

  and eval_complex_cmd config2 program =  match program with
     | (JMP label)::_ -> eval env config2 (env#labeled label)
     | (CJMP (mode, label))::next ->
        let top::rest = ds in
        let goto = (env#labeled label) in
        let target = if ((mode="z") == (Value.to_int top = 0)) then goto else next in
        eval env (cs, rest, subconf) target
     | (CALL (name, args_amount, should_return))::next ->
        if env#is_label name
        then eval env ((next, state)::cs, ds, subconf) (env#labeled name)
        else
          let after_builtin = env#builtin config2 name args_amount (should_return)
          in eval env after_builtin next
     | (BEGIN (_, args, locals))::next ->
        let state_pre = State.enter state (args @ locals) in
        let (args_values,  stack') = split (List.length args) ds in
        let state_arged = List.fold_right2 State.update args args_values state_pre in
        eval env (cs, stack', (state_arged, inp, out, foo)) next
     | RET _::_
     | END::_ -> (match cs with
                 | (prev_prog, prev_state)::rest_cs ->
                    let state_after = State.leave state prev_state in
                    eval env (rest_cs, ds, (state_after, inp, out, foo)) prev_prog
                 | [] -> config2)
     | (ENTER args)::next ->
        let state_pre = State.push state State.undefined args in
        let (args_values,  stack') = split (List.length args) ds in
        let state_arged = List.fold_right2 State.update args args_values state_pre in
        eval env (cs, stack', (state_arged, inp, out, foo)) next
     | LEAVE::next -> eval env (cs, ds, (State.drop state, inp, out, foo)) next
     | (CZCLEARJMP (label, depth))::next ->
        let top::stack' = ds in
        if Value.to_int top = 0
        then let (_,  stack'') = split depth stack' in
             let goto = (env#labeled label) in
             eval env (cs, stack'', subconf) goto
        else eval env (cs, stack', subconf) next        
     | cmd::rest -> eval env (eval_cmd config2 cmd) rest

  in match program with
     | [] -> config2
     | cmd::_ ->
        (* Printf.eprintf "Executing %s with stack [%s]\n" (show insn cmd) (String.concat " , " (List.map Value.v2s ds)); *)
        eval_complex_cmd config2 program

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
  let (_, _, (_, _, o, _)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o, _)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           (* MODIFIED: arguments are already reversed *)
           let (st, i, o, r) = Builtin.eval (st, i, o, None) (args) f in
           (* MOFIDIED: true means should return *)
           let stack'' = if p then let Some r = r in r::stack' else stack' in
           (cstack, stack'', (st, i, o, None))
       end
      )
      ([], [], (State.empty, i, [], None))
      p
  in
  o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let soi = string_of_int
let rec list_init i n = let x = i+1 in if i < n then i::(list_init x n) else []
class compiler =
  object (self)
    val label_count = 0
    val caseof_count = 0
    val cur_patterns_count = 0

    method next_label = {< label_count = label_count+1 >}
                          
    method suffix = soi label_count 
    method get_if_labels =
      "else_" ^ self#suffix, "fi_" ^ self#suffix, self#next_label
    method get_while_labels =
      "loop_" ^ self#suffix, "od_" ^ self#suffix, self#next_label
    method get_opt_while_labels =
      "loop_" ^ self#suffix, "checkwhile_" ^ self#suffix, self#next_label
    method get_repeatuntil_label =
      "repeat_" ^ self#suffix, self#next_label

    method get_caseof_labels amount =
      let variant_label index = "pattern_" ^ self#suffix ^ soi index in
      (List.map variant_label (list_init 0 amount),
       variant_label amount, "esac_" ^ self#suffix,
       self#next_label)
  end

(* TODO *)
let element_at_top_destructive index = [CONST index; SWAP; CALL (".elem", 2, true)]
let element_at_top index = [DUP] @ element_at_top_destructive index

let rec compile_matcher next_label depth pattern = match pattern with
  | Stmt.Pattern.Ident var -> [DROP]
  | Stmt.Pattern.Wildcard -> [DROP]
  | Stmt.Pattern.Sexp (name, subsexps) ->
     [DUP; TAG name; CZCLEARJMP (next_label, depth)] @
       let compile_subpattern index subpattern = element_at_top index @ compile_matcher next_label (depth + 1) subpattern in
       List.concat (List.mapi compile_subpattern subsexps) @ [DROP]

                                                               
let rec compile_binding pattern =
  (* cannot get why it should work; will note it in PR *)
  (* match pattern with
   * | Stmt.Pattern.Ident var -> [SWAP]
   * | Stmt.Pattern.Wildcard -> [DROP]
   * | Stmt.Pattern.Sexp (_, subsexps) ->
   *    let compile_subpattern index subpattern = element_at_top index @ compile_binding subpattern in
   *    (List.concat (List.mapi compile_subpattern subsexps)) @ [DROP] *)
  let rec collect_var_pathes pat = match pat with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident var -> [[]] (* single identifier is the endpoint *)
    | Stmt.Pattern.Sexp (_, subsexps) ->
       let continue_pathes i sub = List.map (fun arr -> i::arr) (collect_var_pathes sub) in
       List.concat (List.mapi continue_pathes subsexps)
  in
  (* assume initial value on stack top *)
  let extract_bind_value path = [DUP] @ (List.concat (List.map element_at_top_destructive path)) @ [SWAP] in
  (* compute bindings in reverse order *)
  let var_pathes = List.rev (collect_var_pathes pattern) in
  List.concat (List.map extract_bind_value var_pathes)
  (* now stack is like [a_1...a_n value@stacktop] *)

let rec compile (defs, main) =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s -> [STRING s]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op] 
  | Expr.Call (name, args_exprs) -> (* has return value *)
     let args_init = List.concat (List.rev (List.map expr args_exprs))
     in args_init @ [CALL (name, List.length args_exprs, true)]
  | Expr.Array args_exprs ->  List.concat (List.rev (List.map expr args_exprs)) @
                               (* now arguments are pushed in correct order *)
                               [CALL (".array", (List.length args_exprs), true)]
  | Expr.Elem (arr, index) -> expr index @ expr arr @ [CALL (".elem", 2, true)]
  | Expr.Length (arr) -> expr arr @ [CALL (".length", 1, true)]
  | Expr.Sexp (name, subexps) -> (List.concat (List.rev (List.map expr subexps))) @ [SEXP (name, List.length subexps)]
  in
  (* it's slow (n^2 for full program) but only at compile time *)
  let rec replace_label old_label new_label program = match program with
    | [] -> []
    | LABEL lbl as orig :: rest -> (if lbl = old_label then [] else [orig]) @ replace_label old_label new_label rest
    | JMP lbl :: rest -> (JMP (if lbl = old_label then new_label else lbl)) :: replace_label old_label new_label rest
    | CJMP (mode, lbl) :: rest -> (CJMP (mode, (if lbl = old_label then new_label else lbl))) :: replace_label old_label new_label rest
    | cmd :: rest -> cmd :: replace_label old_label new_label rest in

  let rec compile_impl compiler = function
    | Stmt.Seq (s1, s2)  -> let prog1, compiler' = compile_impl compiler s1 in
                            let prog2, compiler'' = compile_impl compiler' s2 in
                            prog1 @ prog2, compiler''
    | Stmt.Assign (x, indices, e) ->
       (match indices with
       | [] -> expr e @ [ST x], compiler
       | _ -> expr e @ List.concat (List.rev (List.map expr indices))
              @ [STA (x, (List.length indices))], compiler
       )
    | Stmt.Skip -> [], compiler
    | Stmt.If (cond, positive, negative) ->
       let else_label, fi_label, compiler' = compiler#get_if_labels in
       let prog_pos_raw, compiler'' = compile_impl compiler' positive in
       let prog_pos = match (List.rev prog_pos_raw) with
         | LABEL old_label :: _ -> replace_label old_label fi_label prog_pos_raw
         | [] -> []
         | _ -> prog_pos_raw in
       let prog_neg_raw, compiler''' = compile_impl compiler'' negative in
       let prog_neg = match (List.rev prog_neg_raw) with
         | LABEL old_label :: _ -> replace_label old_label fi_label prog_neg_raw
         | [] -> []
         | _ -> prog_neg_raw in
       expr cond @ [CJMP ("z", else_label)]
       @ prog_pos @ [JMP fi_label; LABEL else_label]
       @ prog_neg @ [LABEL fi_label], compiler'''
    | Stmt.While (cond, body) -> 
       let loop_label, check_label, compiler' = compiler#get_opt_while_labels in
       let prog_body, compiler'' = compile_impl compiler' body in       
       [JMP check_label; LABEL loop_label] @ prog_body @ [LABEL check_label]
       @ expr cond @ [CJMP ("nz", loop_label)], compiler''
    | Stmt.Repeat (body, cond) ->
       let loop_label, compiler' = compiler#get_repeatuntil_label in
       let prog_body, compiler'' = compile_impl compiler' body in
       [LABEL loop_label] @ prog_body @ expr cond @ [CJMP ("z", loop_label)], compiler''
    | Stmt.Call (name, args_exprs) ->
       (let args_init = List.concat (List.rev (List.map expr args_exprs)) (* args values on stack top *)
        in args_init @ [CALL (name, List.length args_exprs, false)]), compiler (* no return value *)
    | Stmt.Return opt_value -> (match opt_value with
                               | Some exp -> expr exp @ [RET true]
                               | None -> [RET false]), compiler
    | Stmt.Case (to_match, variants) ->
       let variants_labels, mock_label, esac_label, compiler = compiler#get_caseof_labels (List.length variants) in
       let labels_pairs = List.combine variants_labels (let _::shifted = variants_labels in shifted @ [mock_label]) in
       
       let compile_variant_impl comp (pattern, stmt) (cur_label, next_label) =
         let stmt_body, comp  = compile_impl comp stmt in
         [LABEL cur_label; DUP] @ compile_matcher next_label 1 pattern
         @ [COMMENT "matching ended"] 
         @ (compile_binding pattern) @ [DROP]
          @ [COMMENT "binding ended"]
         @ [ENTER (List.rev (Stmt.Pattern.vars pattern))] @ stmt_body
         @ [LEAVE; JMP esac_label]
         @ [COMMENT "body ended"], comp in 
       let compile_variant (collected, comp) variant pair=
         let variant_body, comp = compile_variant_impl comp variant pair in
         (collected @ variant_body, comp) in
       let merged_variants, compiler = List.fold_left2 compile_variant ([], compiler) variants labels_pairs in
       expr to_match @ merged_variants @ [LABEL mock_label(* ; DROP *); LABEL esac_label],
       compiler
  in
  let main_program, compiler = compile_impl (new compiler) main in
  let compile_procedure (collected, comp) (name, (args, locals, body)) =
    let proc_body, comp  = compile_impl comp body in
    let proc = [LABEL name; BEGIN (name, args, locals)] @ proc_body @ [END] in
    (collected @ proc, comp) in
  let procedures, _ = List.fold_left compile_procedure ([], compiler) defs in
  main_program @ [END] @ procedures
