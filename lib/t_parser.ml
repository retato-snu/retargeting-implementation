(** A concrete-syntax parser for the target language T. *)

open T_encoding

(** Raised on malformed input. *)
exception Parse_error = T_ast.Parse_error

open T_ast

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

(* Free names (unbound by let or parameter) resolve to the implicit id 0. *)
let resolve_var (scope : (string * var_id) list) (name : string) : var_id =
  match List.assoc_opt name scope with Some id -> id | None -> 0

let resolve_fun (st : state) (name : string) : fun_id =
  match List.assoc_opt name st.funs with
  | Some id -> id
  | None ->
      raise
        (Parse_error (Printf.sprintf "call to undefined function %S" name))

let rec label_expr (st : state) (scope : (string * var_id) list) (e : sexpr) :
    expr =
  match e with
  | SInt n -> Int (fresh_label st, n)
  | SVar name -> Var (fresh_label st, resolve_var scope name)
  | SApp (name, arg) ->
      let fid = resolve_fun st name in
      let arg' = label_expr st scope arg in
      App (fresh_label st, fid, arg')
  | SSub (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Sub (fresh_label st, a', b')
  | SMul (a, b) ->
      let a' = label_expr st scope a in
      let b' = label_expr st scope b in
      Mul (fresh_label st, a', b')
  | SLet (name, rhs, body) ->
      let rhs' = label_expr st scope rhs in
      let id = fresh_let_id st in
      let body' = label_expr st ((name, id) :: scope) body in
      Let (fresh_label st, id, rhs', body')
  | SIfz (c, t, e2) ->
      let c' = label_expr st scope c in
      let t' = label_expr st scope t in
      let e2' = label_expr st scope e2 in
      Ifz (fresh_label st, c', t', e2')

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

(** Parse a whole T program. Raises {!Parse_error} on malformed input. *)
let parse_program (src : string) : program =
  let sp = run_parser T_grammar.program src in
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
  let defs =
    List.map
      (fun (d : sdef) ->
        let fid = resolve_fun st d.name in
        let body = label_expr st [ (d.param, 0) ] d.body in
        (fid, body))
      sp.defs
  in
  let main = label_expr st [] sp.main in
  { defs; main }

(** Parse a single T expression; free variables resolve to the implicit id [0]. Raises {!Parse_error}. *)
let parse_expr (src : string) : expr =
  let se = run_parser T_grammar.expr_only src in
  let st = { next_label = 0; next_let_id = 1; funs = [] } in
  label_expr st [] se
