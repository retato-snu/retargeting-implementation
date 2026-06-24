(** Concrete-syntax parser for S: text -> {!S_syntax} core IR (strict-ANF surface). *)

exception Parse_error = S_syntax.Parse_error

let run_parser
    (start : (Lexing.lexbuf -> S_grammar.token) -> Lexing.lexbuf -> 'a)
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

let parse (src : string) : S_syntax.program = run_parser S_grammar.program src

(* cmd_only: no functions declared, so a call [f(...)] is treated as a primitive. *)
let parse_cmd_program (src : string) : S_syntax.program =
  run_parser S_grammar.cmd_only src
