(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec list_init_helper i acc len f = 
  if i < len
  then list_init_helper (i+1) (acc @ [f i]) len f
  else acc

let list_init len f = list_init_helper 0 [] len f

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
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
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
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
    
    let rec eval env ((st, i, o, r) as conf) = function
    | Const c -> 
      (st, i, o, Some (Value.of_int c))
    | Array xs -> 
      let st', i', o', args = eval_list env conf xs
      in env#definition env ".array" args (st', i', o', None)
    | Sexp (s, xs) ->
      let st', i', o', args = eval_list env conf xs in
      (st', i', o', Some (Value.sexp s args))
    | String s -> 
      (st, i, o, Some (Value.of_string s))
    | Var v -> 
      (st, i, o, Some (State.eval st v))
    | Binop (op, x, y) ->
      let (_, _, _, Some x') as conf' = eval env conf x in
      let (st', i', o', Some y') = eval env conf' y in
      (st', i', o', Some (Value.of_int (to_func op (Value.to_int x') (Value.to_int y'))))
    | Elem (b, j) ->
      let (st', i', o', args) = eval_list env conf [b; j]
      in env#definition env ".elem" args (st', i', o', None)
    | Length l -> 
      let (st', i', o', Some r) = eval env conf l
      in env#definition env ".length" [r] (st', i', o', None)
    | Call (f, xs) ->
      let (st', i', o', args) = eval_list env conf xs
      in env#definition env f args (st', i', o', None)
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
    ostap (
      parse:
      !(Ostap.Util.expr 
        (fun x -> x)
        (
          Array.map (
            fun (a, s) -> a, 
            List.map (
              fun s -> ostap(- $(s)), 
              (fun x y -> Binop (s, x, y))
            ) s
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
        v:primary' "." %"length" {Length v}
        | primary' ;
      
      primary':
        v:core k:(-"[" parse -"]")*
        {List.fold_left (fun v' k' -> Elem (v', k')) v k }
      | core ;

      core:
        call
      | n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | c:CHAR    {Const (Char.code c)}
      | s:STRING  {String (String.sub s 1 @@ String.length s - 2)}
      | "`" s:IDENT "(" l:!(Util.list parse) ")" {Sexp (s, l)}
      | "`" s:IDENT                              {Sexp (s, [])}
      | "[" a:!(Util.list parse) "]" {Array a}
      | -"(" parse -")";

      call: x:IDENT "(" params:!(Ostap.Util.listBy)[ostap (",")][parse]? ")" 
        {Call (x, match params with Some s -> s | None -> [])}
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
          parse:
            %"_" {Wildcard}
          | "`" s:IDENT "(" l:!(Util.list parse) ")" {Sexp (s, l)}
          | "`" s:IDENT {Sexp (s, [])}
          | s:IDENT {Ident s}
        )
        
        let vars p =
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

         val eval : des -> a -> mod -> config

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
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k = 
      let merge s1 s2 = match s2 with Skip -> s1 | _ -> Seq (s1, s2) in
      function
      | Assign (x, es, e) -> 
        let (st', i', o', args) = Expr.eval_list env conf es in
        let (st'', i'', o'', Some v) = Expr.eval env (st', i', o', None) e in
        eval env (update st'' x v args, i'', o'', None) Skip k
      | Seq (s1, s2) ->
        eval env conf (merge s2 k) s1
      | Skip -> 
        (match k with Skip -> conf | _ -> eval env conf Skip k)
      | If (e, ts, fs) ->
        let (st', i', o', Some v) = Expr.eval env conf e in
        eval env (st', i', o', None) k (if Value.to_int v <> 0 then ts else fs)
      | While (e, s)      ->
        eval env conf k (If (e, Seq(s, While(e, s)), Skip))
      | Repeat (s, e)     ->
        eval env conf k (Seq (s, If (e, Skip, Repeat (s, e))))
      | Case (e, pl) ->
        let (st', i', o', Some v) = Expr.eval env conf e in
        let rec isMatching = function
        | (Pattern.Wildcard, _) -> true
        | (Pattern.Ident _,  _) -> true
        | (Pattern.Sexp(s, ps), Value.Sexp(s', ps')) when s = s' -> 
          List.length ps = List.length ps'
          && List.fold_left (fun acc p -> acc && isMatching p) true @@ List.combine ps ps'
        | _ -> false
        in
        let rec findMatch = function
        | (p, s)::cases -> if isMatching (p, v) then Some(p, s) else findMatch cases
        | [] -> None
        in
        let rec assign state = function
        | (Pattern.Ident x, v) -> State.bind x v state
        | (Pattern.Sexp (_, ps), Value.Sexp(_, ps')) -> List.fold_left assign state @@ List.combine ps ps'
        | _ -> state
        in 
        (match findMatch pl with
        | None -> eval env (st', i', o', None) Skip k
        | Some (p, s) ->
          let st'' = assign State.undefined (p, v) in
          eval env (State.push st' st'' (Pattern.vars p), i', o', None) k s)
      | Return opte       ->
        (match opte with Some e -> Expr.eval env conf e | None -> conf)
      | Call (name, args) ->
        eval env (Expr.eval env conf (Expr.Call (name, args))) Skip k
      | Leave ->
        eval env (State.drop st, i, o, None) Skip k
                                                        
    (* Statement parser *)
    let nested_elifs elifs els =
      let last = 
        match els with
        | Some s -> s
        | None   -> Skip
      in List.fold_right (fun (c, s) ss -> If (c, s, ss)) elifs last

    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;

      branch: p:!(Pattern.parse) "->" s:parse {p, Seq(s, Leave)};

      stmt:
        c:!(Expr.call)                   {match c with Expr.Call(f, args) -> Call(f, args)}
      | x:IDENT 
        ks:(-"[" !(Expr.parse) -"]")*
        ":=" e:!(Expr.parse)             {Assign (x, ks, e)}
      | %"skip"                          {Skip}
      | %"if" c:!(Expr.parse) 
        %"then" ts:!(parse)
        elifs:(%"elif" !(Expr.parse) %"then" parse)*
        els:(%"else" parse)? 
        %"fi"                            {If (c, ts, nested_elifs elifs els)}
      | %"while" c:!(Expr.parse) 
        %"do" s:parse %"od"              {While(c, s)}
      | %"repeat" s:parse
        %"until" c:!(Expr.parse)         {Repeat(s, c)}
      | %"case" e:!(Expr.parse) %"of"
        pl:!(Util.listBy (ostap ("|")) branch)
        %"esac"                          {Case(e, pl)}
      | %"for" is:parse 
        "," c:!(Expr.parse)
        "," ss:parse 
        %"do" s:parse %"od"              {Seq(is, While(c, Seq(s, ss)))}
      | %"return" e:!(Expr.parse)?       {Return e}
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
