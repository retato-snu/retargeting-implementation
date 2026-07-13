(** A concrete-syntax parser for the target language T, so that tests and demos
    can write T programs as source rather than hand-constructing labeled ASTs. An
    [ocamllex] lexer ({!T_lexer}) feeds an [ocamlyacc] grammar ({!T_grammar})
    that builds the label-less surface AST of {!T_ast}, and the labeling pass
    below assigns the integer ids and fresh labels {!T_encoding} expects.

    {2 Concrete syntax}

    {v
      program ::= { def } expr
      def     ::= ident '(' ident ')' '=' expr ';'

      expr    ::= 'let' ident '=' expr 'in' expr
                | 'ifz' expr 'then' expr 'else' expr
                | add                                  (* additive level *)

      add     ::= mul { ('+' | '-') mul }              (* left-associative *)
      mul     ::= atom { '*' atom }                    (* left-associative *)

      atom    ::= integer
                | ident                                (* variable occurrence *)
                | ident '(' expr ')'                   (* application f(e) *)
                | '(' expr ')'
    v}

    [+] is {!T_encoding.Add}, [-] is {!T_encoding.Sub} and [*] is
    {!T_encoding.Mul}; all are left-associative and [*] binds tighter, as in
    ordinary arithmetic. Keywords are [let], [in], [ifz], [then], [else].

    {2 Identifiers and scope}

    The labeling pass maps surface names to ids by the conventions of
    {!Interp_st} and {!T_machine}, so that a parsed program runs unchanged
    through either evaluator: the formal parameters of a function are the
    implicit variables [0 .. k-1] (the paper's [x_arg] is the id [0]), a free
    name in [main] — the external input — also resolves to id [0], and let-bound
    variables get fresh ids that never collide with them, resolved lexically to
    the innermost binding in scope. Function names get distinct
    {!T_encoding.fun_id}s in definition order, starting at [0], and forward
    references are allowed. Every expression node gets a fresh {!Label.t} from a
    per-parse counter. Malformed input raises {!Parse_error}. *)

open T_encoding

(** Raised on malformed input. (Defined in {!T_ast} so the generated lexer can
    raise it; re-exported here under the public name.) *)
exception Parse_error = T_ast.Parse_error

(* The label-less surface AST built by the grammar. *)
open T_ast

(** {1 Labeling pass}

    Lower the surface AST into the labeled {!T_encoding} core: assign each node a
    fresh label, resolve variable occurrences to ids (lexically, with free names
    falling through to the implicit id [0]), and resolve call heads to function
    ids in definition order. *)

(* Per-parse state: a fresh-label counter, a fresh-let-id counter (starting at
   [1] so let-ids never clash with the implicit parameter [0]), and the
   function-name table, in definition order. *)
type state = {
  mutable next_label : Label.t;
  mutable next_let_id : var_id;
  funs : (string * fun_id) list;
}

let fresh_label (st : state) : Label.t =
  let l = st.next_label in
  st.next_label <- l + 1;
  l

let fresh_let_id (st : state) : var_id =
  let x = st.next_let_id in
  st.next_let_id <- x + 1;
  x

(* Resolve a variable name against the lexical scope (innermost binding first); a
   name bound by no [let] and no parameter is the implicit id [0]. *)
let resolve_var (scope : (string * var_id) list) (name : string) : var_id =
  match List.assoc_opt name scope with Some id -> id | None -> 0

(* Resolve a call head against the definition-order function table. *)
let resolve_fun (st : state) (name : string) : fun_id =
  match List.assoc_opt name st.funs with
  | Some id -> id
  | None ->
      raise
        (Parse_error (Printf.sprintf "call to undefined function %S" name))

(* Lower a surface expression in lexical scope [scope]. Labels are assigned in a
   left-to-right traversal; let-ids are allocated at the binding site, outer
   before inner. *)
let rec label_expr (st : state) (scope : (string * var_id) list) (e : sexpr) :
    expr =
  match e with
  | SInt n -> Int (fresh_label st, n)
  | SVar name -> Var (fresh_label st, resolve_var scope name)
  | SApp (name, arg) ->
      (* The head must name a defined function; it is resolved before the
         argument is lowered and the node's own label taken last. *)
      let fid = resolve_fun st name in
      let arg' = label_expr st scope arg in
      App (fresh_label st, fid, arg')
  | SApp2 (name, a1, a2) ->
      let fid = resolve_fun st name in
      let a1' = label_expr st scope a1 in
      let a2' = label_expr st scope a2 in
      App2 (fresh_label st, fid, a1', a2')
  | SApp3 (name, a1, a2, a3) ->
      let fid = resolve_fun st name in
      let a1' = label_expr st scope a1 in
      let a2' = label_expr st scope a2 in
      let a3' = label_expr st scope a3 in
      App3 (fresh_label st, fid, a1', a2', a3')
  | SAdd (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Add (fresh_label st, a', b')
  | SSub (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Sub (fresh_label st, a', b')
  | SMul (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Mul (fresh_label st, a', b')
  | SDiv (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Div (fresh_label st, a', b')
  | SMod (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Mod (fresh_label st, a', b')
  | SLt (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Lt (fresh_label st, a', b')
  | SLet (name, rhs, body) ->
      let rhs' = label_expr st scope rhs in
      (* The bound variable gets a fresh id, in scope only in the body. *)
      let id = fresh_let_id st in
      let body' = label_expr st ((name, id) :: scope) body in
      Let (fresh_label st, id, rhs', body')
  | SIfz (c, t, e2) ->
      let c' = label_expr st scope c in
      let t' = label_expr st scope t in
      let e2' = label_expr st scope e2 in
      Ifz (fresh_label st, c', t', e2')

(** {1 Lexer / parser glue} *)

(* Run the grammar entry [start] over [src], translating ocamlyacc's failures
   into the module's {!Parse_error}. *)
let run_parser (start : (Lexing.lexbuf -> T_grammar.token) -> Lexing.lexbuf -> 'a)
    (src : string) : 'a =
  let lexbuf = Lexing.from_string src in
  try start T_lexer.token lexbuf
  with Parsing.Parse_error ->
    let p = Lexing.lexeme_start_p lexbuf in
    let line = p.Lexing.pos_lnum in
    let col = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
    raise
      (Parse_error
         (Printf.sprintf "parse error at line %d, column %d" line col))

(** {1 Entry points} *)

(** Parse a whole T program. To allow forward references the function table is
    built from the definition headers first (rejecting duplicates), then each
    body and the main expression are labeled against it. *)
let parse_program (src : string) : program =
  let sp = run_parser T_grammar.program src in
  (* Assign fun ids in definition order, rejecting duplicates. *)
  let funs =
    List.fold_left
      (fun acc (d : sdef) ->
        if List.mem_assoc d.name acc then
          raise
            (Parse_error
               (Printf.sprintf "duplicate function definition %S" d.name));
        acc @ [ (d.name, List.length acc) ])
      [] sp.defs
  in
  let st = { next_label = 0; next_let_id = 1; funs } in
  (* Bodies are labeled in definition order, then main, so labeling is
     deterministic. *)
  let defs =
    List.map
      (fun (d : sdef) ->
        let fid = resolve_fun st d.name in
        (* Bind the k formal parameters to the ids [0 .. k-1] left to right (the
           implicit-id-0 convention extended to arity k). *)
        let scope = List.mapi (fun i name -> (name, i)) d.params in
        (* Let-ids must not collide with those parameter ids, so start them at
           [k] or above; the shared counter is monotone, so for the arity-1
           bodies of the original language its baseline of 1 is unchanged. *)
        if st.next_let_id < List.length d.params then
          st.next_let_id <- List.length d.params;
        let body = label_expr st scope d.body in
        (fid, body))
      sp.defs
  in
  let main = label_expr st [] sp.main in
  { defs; main }

(** Parse a single T expression in an empty variable scope (free variables resolve
    to the implicit id [0]) with no function definitions, so a call [f(e)] fails
    as an undefined function. Convenient for tests. *)
let parse_expr (src : string) : expr =
  let se = run_parser T_grammar.expr_only src in
  let st = { next_label = 0; next_let_id = 1; funs = [] } in
  label_expr st [] se
