(** Concrete-syntax parser for source language S: lex/parse to a surface AST, then A-normalize into the strict-ANF {!S_syntax} core. *)

exception Parse_error = S_ast.Parse_error

module Surface = S_ast

let is_upper c = c >= 'A' && c <= 'Z'

type norm_state = {
  fun_names : string list;
  mutable next_label : Label.t;
  mutable next_temp : int;
  mutable ctrl : (Label.t * S_syntax.cmd) list;
}

let fresh_label (ns : norm_state) : Label.t =
  let l = ns.next_label in
  ns.next_label <- l + 1;
  l

(* Reserved [%]-prefix keeps temporaries distinct from any source identifier. *)
let fresh_temp (ns : norm_state) : string =
  let t = ns.next_temp in
  ns.next_temp <- t + 1;
  Printf.sprintf "%%t%d" t

let emit (ns : norm_state) (c : S_syntax.cmd) : Label.t =
  let l = fresh_label ns in
  ns.ctrl <- (l, c) :: ns.ctrl;
  l

let is_declared_fun (ns : norm_state) (name : string) : bool =
  List.mem name ns.fun_names

let rec norm_atom (ns : norm_state) (e : Surface.expr) (k : Label.t) :
    S_syntax.atom * Label.t =
  match e with
  | Surface.Int n -> (S_syntax.AInt n, k)
  | Surface.Var x -> (S_syntax.AVar x, k)
  | Surface.App _ ->
      let x = fresh_temp ns in
      let entry = norm_bind ns x e k in
      (S_syntax.AVar x, entry)

(* Operands normalized right-to-left so run-time control evaluates them in source order before [k]. *)
and norm_atoms (ns : norm_state) (es : Surface.expr list) (k : Label.t) :
    S_syntax.atom list * Label.t =
  match es with
  | [] -> ([], k)
  | e :: rest ->
      let rest_atoms, rest_entry = norm_atoms ns rest k in
      let a, entry = norm_atom ns e rest_entry in
      (a :: rest_atoms, entry)

and norm_bind (ns : norm_state) (x : string) (e : Surface.expr) (k : Label.t) :
    Label.t =
  match e with
  | Surface.Int _ | Surface.Var _ ->
      let a, entry = norm_atom ns e k in
      (* [entry = k] for an atom; the binding command becomes the new entry. *)
      ignore entry;
      emit ns (S_syntax.Let (x, S_syntax.Atom a, k))
  | Surface.App (head, args) ->
      if is_upper_head head then (
        let l = emit ns (S_syntax.LetTag (x, head, [], k)) in
        let atoms, entry = norm_atoms ns args l in
        patch_lettag ns l x head atoms k;
        entry)
      else if is_declared_fun ns head then (
        let l = emit ns (S_syntax.LetCall (x, head, [], k)) in
        let atoms, entry = norm_atoms ns args l in
        patch_letcall ns l x head atoms k;
        entry)
      else
        let l = emit ns (S_syntax.Let (x, S_syntax.Prim (head, []), k)) in
        let atoms, entry = norm_atoms ns args l in
        patch_prim ns l x head atoms k;
        entry

and is_upper_head (head : string) : bool =
  String.length head > 0 && is_upper head.[0]

(* Application commands are emitted before operands so operands can continue to them; the placeholder is rewritten in place once atoms are known. *)
and replace (ns : norm_state) (l : Label.t) (c : S_syntax.cmd) : unit =
  ns.ctrl <- (l, c) :: List.remove_assoc l ns.ctrl

and patch_prim ns l x head atoms k =
  replace ns l (S_syntax.Let (x, S_syntax.Prim (head, atoms), k))

and patch_letcall ns l x head atoms k =
  replace ns l (S_syntax.LetCall (x, head, atoms, k))

and patch_lettag ns l x head atoms k =
  replace ns l (S_syntax.LetTag (x, head, atoms, k))

let rec norm_cmd (ns : norm_state) (c : Surface.cmd) : Label.t =
  match c with
  | Surface.Return e ->
      let l = emit ns (S_syntax.Return (S_syntax.AInt 0)) in
      let a, entry = norm_atom ns e l in
      replace ns l (S_syntax.Return a);
      entry
  | Surface.Let (x, e, body) ->
      let body_entry = norm_cmd ns body in
      norm_bind ns x e body_entry
  | Surface.Match (scrut, branches) ->
      let core_branches =
        List.map
          (fun ((tag, binders), body) ->
            let body_entry = norm_cmd ns body in
            (S_syntax.PTag (tag, binders), body_entry))
          branches
      in
      emit ns (S_syntax.Match (S_syntax.AVar scrut, core_branches))

let norm_fundef (ns : norm_state) (d : Surface.fundef) : S_syntax.fundef =
  let entry = norm_cmd ns d.Surface.body in
  { S_syntax.name = d.Surface.name; params = d.Surface.params; entry }

let normalize (sp : Surface.program) : S_syntax.program =
  let fun_names = List.map (fun d -> d.Surface.name) sp.Surface.funs in
  let ns = { fun_names; next_label = 0; next_temp = 0; ctrl = [] } in
  let funs = List.map (norm_fundef ns) sp.Surface.funs in
  let main = norm_cmd ns sp.Surface.main in
  { S_syntax.funs; ctrl = S_syntax.ctrl_of_list ns.ctrl; main }

let run_parser (start : (Lexing.lexbuf -> S_grammar.token) -> Lexing.lexbuf -> 'a)
    (src : string) : 'a =
  let lexbuf = Lexing.from_string src in
  try start S_lexer.token lexbuf
  with Parsing.Parse_error ->
    let p = Lexing.lexeme_start_p lexbuf in
    let line = p.Lexing.pos_lnum in
    let col = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
    raise
      (Parse_error
         (Printf.sprintf "parse error at line %d, column %d" line col))

let parse (src : string) : S_syntax.program =
  normalize (run_parser S_grammar.program src)

let parse_cmd_program (src : string) : S_syntax.program =
  let c = run_parser S_grammar.cmd_only src in
  normalize { Surface.funs = []; main = c }
