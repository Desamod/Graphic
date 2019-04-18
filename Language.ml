(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
(* open Option *)

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let is_some = function
  | Some _ -> true
  | None -> false
              
(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let rec v2s = function
      | Int i -> Printf.sprintf "%d" i
      | String bs -> Bytes.to_string bs
      | Array vals -> Printf.sprintf "[%s]" (String.concat ", " (Array.to_list (Array.map v2s vals)))
      | Sexp (name, vals) -> Printf.sprintf "%s{%s}" name (String.concat ", " (List.map v2s vals))

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
                      
  end


let to_list = function
  | None -> []
  | Some results -> results

       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | ".string"      ->
       let make_string str = Some (Value.String (Bytes.of_string str)) in
       let rec convert value = 
         match value with
         | (Value.String bytes as str) ->
            Printf.sprintf "\"%s\"" (Bytes.to_string bytes)
         | (Value.Int num) -> string_of_int num
         | (Value.Array elements) ->
            let elements = String.concat ", " (List.map convert (Array.to_list elements)) in
            Printf.sprintf "[%s]" elements
         | (Value.Sexp (name, elements)) ->
            if (List.length elements != 0)
            then let elements = String.concat ", " (List.map convert elements) in
                 Printf.sprintf "`%s (%s)" name elements
            else Printf.sprintf "`%s" name
       in (st, i, o, make_string (convert (List.hd args)))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))
    | x -> failwith (Printf.sprintf "Unknown fun: %s" x)
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator
          val eval : env -> config -> t -> int * config
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
           method definition : env -> string -> int list -> config -> config
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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

    let e2s = GT.transform(t) (new @t[show]) ()
    let el2sl es = String.concat ", " (List.map e2s es)
    let log_call name args_exprs = prerr_endline (Printf.sprintf "Calling %s with [%s]" name (el2sl args_exprs))                         
    
    let rec eval env ((st, i, o, (r : Value.t option)) as conf) expr =
      let set_result res = (st, i, o, Some res) in
      match expr with
      | Const n -> set_result (Value.of_int n)
      | Var   x -> set_result (State.eval st x)
      | Binop (op, x, y) ->
         let (st', i', o', Some (Value.Int a1) as after_first) = eval env conf x in
         let (st'', i'', o'', Some (Value.Int a2)) = eval env after_first y in
         let result = to_func op (a1) (a2) in
         (st'', i'', o'', Some (Value.of_int result))
      | Call (func, args_exprs) ->
         (* let _ = log_call func args_exprs in *)
         let (st', i', o', args_values) = eval_list env conf args_exprs in
         env#definition env func args_values (st', i', o', None)
      | String str -> set_result (Value.of_string (Bytes.of_string str))
      | Array exprs ->
         let (st', i', o', values) = eval_list env conf exprs in
         env#definition env ".array" values (st', i', o', None)
      | Elem (seq_expr, index_expr) -> 
         let (st', i', o', args) = eval_list env conf [seq_expr; index_expr]
         in env#definition env ".elem" args (st', i', o', None)
      | Length expr ->
         let (st', i', o', Some value) = eval env conf expr
         in env#definition env ".length" [value] (st', i', o', None)
      | Sexp (name, subexps) ->
         let (st', i', o', subvalues) = eval_list env conf subexps in         
         (st', i', o', Some (Value.Sexp (name, subvalues)))
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let rec build_index_sequence expr indices = match indices with
      | [] -> expr
      | index::rest -> build_index_sequence (Elem (expr, index)) rest

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
      
      args_list: -"(" !(Util.list0)[parse] -")";
      funcall: fnc:IDENT args:args_list {Call (fnc, args)};

      sexp: "`" name:IDENT subs_opt:((-"(" (!(Util.list)[parse]) -")")?)
                                      {match subs_opt with
                                         Some subs -> Sexp (name, subs)
                                       | None -> Sexp (name, [])};

      main: (* no left recursion *)
        -"(" parse -")"
        | funcall
        | sexp
        | n:DECIMAL {Const n}
        | x:IDENT   {Var x}
        | "[" elements:!(Util.list0)[parse] "]" {Array elements}
        | s:STRING {String (String.sub s 1 ((String.length s)-2))}
        | c:CHAR {Const (Char.code c)};

          (* index:  {ix}; *)
      indices_seq: inds:((-"[" parse -"]")*) {inds};
      indexed: arr:main inds:indices_seq {match inds with
                                          | [] -> arr
                                          | _ -> build_index_sequence arr inds};
      primary:
        ixd:(arr:indexed len_opt:".length"? {match len_opt with | Some _ -> Length arr | None -> arr}) str_opt:".string"? {match str_opt with | Some _ -> Call (".string", [ixd]) | None -> ixd}
    )    
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          wildcard: "_" {Wildcard};
          sexp: "`" name:IDENT subs_opt:((-"(" (!(Util.list)[parse]) -")")?)
                                          {match subs_opt with Some subs -> Sexp (name, subs) | None -> Sexp (name, [])};
          var: name:IDENT {Ident name};
          parse: wildcard | sexp | var
        )
        
        let vars p =
          (* transform(t) (fun f -> object inherit [string list, _] @t[foldl] f method c_Ident s _ name = name::s end) [] p          *)
          (* definition above doesn't compile, use one from video *)
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
           ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec match_pattern value pattern = match pattern with
      | Pattern.Wildcard -> Some []
      | Pattern.Ident var -> Some [(var, value)]
      | Pattern.Sexp (name, subpatterns) ->
         match value with
         | Value.Sexp (name', subvalues) ->
            if (name = name') && (List.length subpatterns = List.length subvalues)
            then
              let subresults = List.map2 match_pattern subvalues subpatterns in
              if List.for_all (is_some) subresults
              then
                Some (List.concat (List.map (fun (Some lst) -> lst) subresults))
              else None
            else None
         | _ -> failwith "Tried to match pattern with non-sexp"

    let rec eval env (state, input, output, (res : Value.t option) as config) kontinue program =
      let eval_expr_now expr = Expr.eval env config expr in
      let set_var var value = State.update var value state in
      let prepend_kontinue stmt kont = match kont with
        | Skip -> stmt
        | _ -> Seq (stmt, kont) in
      match program with
      | Skip -> (match kontinue with
                | Skip -> config
                | _ -> eval env config Skip kontinue)
      | Assign (var, indices, expr) ->
         let (st', i', o', args_values) = Expr.eval_list env config indices in
         let (st'', i'', o'', Some value) = Expr.eval env (st', i', o', None) expr in
         let st''' = update st'' var value args_values in
         eval env (st''', i'', o'', None) Skip kontinue
      | Seq (prog1, prog2) ->         
         eval env config (prepend_kontinue prog2 kontinue) prog1
      | If (cond, positive, negative) ->
         let (_, _, _, Some (Value.Int res) as after_cond_eval) = eval_expr_now cond in
         if (res !=0)
         then eval env after_cond_eval kontinue positive
         else eval env after_cond_eval kontinue negative
      | (While (cond, body) as loop) ->
         let (_, _, _, Some (Value.Int res) as after_cond_eval) = eval_expr_now cond in
         if (res!=0)
         then eval env after_cond_eval (prepend_kontinue loop kontinue) body
         else eval env after_cond_eval Skip kontinue
      | (Repeat (body, cond) as loop) ->
         let config' = eval env config Skip body in
         let (_, _, _, Some (Value.Int res) as after_cond_eval) = Expr.eval env config' cond in
         if res == 0
         then (* then eval env after_cond_eval kontinue loop *)
           eval env after_cond_eval (prepend_kontinue loop kontinue) Skip
         else eval env after_cond_eval Skip kontinue
      | Case (expr, variants) ->
         (let (st', i', o', Some value as after_eval) = eval_expr_now expr in
         try
           let try_match (pattern, stmt) = match (match_pattern value pattern) with
             | Some lst -> Some (lst, stmt)
             | None -> None in
           let (Some (branch_locals, stmt)) = List.find (is_some) (List.map try_match variants) in
           let (bl_vars, _) = List.split branch_locals in
           let branch_state_pre = List.fold_left (fun st (var, value) -> State.update var value st) (State.push state State.undefined bl_vars) branch_locals in
           let (st'', i'', o'', res'') = eval env (branch_state_pre, i', o', None) Skip stmt in
           (* let st''' = State.leave st'' branch_state_pre in *)
           let st''' = State.drop st'' in
           eval env (st''', i'', o'', res'') Skip kontinue
         with Not_found -> failwith "Pattern matching failed"
         )
      | Call (name, args_exprs) ->
         (* let _ = Expr.log_call name args_exprs in *)
         let (st', i', o', args_values) = Expr.eval_list env config args_exprs in
         let after_call = env#definition env name args_values (st', i', o', None) in
         eval env after_call Skip kontinue
      | Return opt -> match opt with
                      | Some expr -> eval_expr_now expr
                      | None -> config
                                                        
    (* Statement parser *)
    let rec build_ite_tree (cond, positive as if_branch) elif_branches else_branch_opt =
      match elif_branches, else_branch_opt with
      | elif::rest, _ ->
         let subtree = build_ite_tree elif rest else_branch_opt in
         If (cond, positive, subtree)
      | [], None -> If (cond, positive, Skip)
      | [], Some else_cmd -> If (cond, positive, else_cmd)

    ostap (	  
      base: !(Expr.parse);
      pattern: !(Pattern.parse);

      assign: v:IDENT inds:(!(Expr.indices_seq)) ":=" e:base {Assign (v, inds, e)};
      (* read: "read" "(" v:IDENT ")" {Read v};
       * write: "write" "(" e:base ")" {Write e}; *)
      skip: "skip" {Skip};
      args_list: arg:base "," rest:args_list {arg::rest} | arg:base {[arg]};
      call: name:IDENT "(" args:(args_list?) ")" {Call (name, to_list args)};
      return: "return" opt_expr:(base?) {Return opt_expr};
      (* single: assign | read | write | skip | call | return; *)
      single: assign | skip | call | return;

      if_then_branch: "if" cond:base "then" positive:parse {(cond, positive)};
      elif_branch: "elif" cond:base "then" positive:parse {(cond, positive)};
      else_branch: "else" negative:parse {negative};
      ite: itb:if_then_branch elifbs:(elif_branch*) ebopt:(else_branch?) "fi" {build_ite_tree itb elifbs ebopt};
      while_loop: "while" cond:base "do" body:parse "od" {While (cond, body)};
      repeat_loop: "repeat" body:parse "until" cond:base {Repeat (body, cond)};
      for_loop: "for" init:parse "," cond:base "," update:parse "do" body:parse "od" {Seq (init, While (cond, Seq (body, update)))};
      pattern_match: p:pattern "->" result:parse {(p, result)};
      caseof: "case" value:base "of" branches:(!(Util.listBy)[ostap ("|")][pattern_match]) "esac" {Case (value, branches)};
      grouped: ite | while_loop | repeat_loop | for_loop | caseof;
      seq: cmd1:(single | grouped)  ";" cmd2:parse {Seq (cmd1, cmd2)};

      parse: seq | grouped | single
    )      
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             (* let _ = log_call f args in *)
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))