(** A concrete-syntax parser for the source language S, so that tests and demos
    can write S programs as readable source rather than hand-constructing labeled
    ASTs. An [ocamllex] lexer ({!S_lexer}) feeds an [ocamlyacc] grammar
    ({!S_grammar}) that builds the {!S_syntax} core IR {b directly}: no surface
    AST, no normalization pass. The grammar allocates a fresh {!Label.t} per
    command and per constructor allocation site, classifies each let right-hand
    side at force-time, and accumulates the [label -> command] control map itself
    (resetting its per-parse state from an empty leading marker), so this module
    is only a thin wrapper that runs an entry point and returns the
    {!S_syntax.program}. The [main] entry and each function entry are the labels
    of their first commands.

    {2 Concrete syntax}

    {v
      prog ::= { 'def' ident '(' [ ident { ',' ident } ] ')' '=' cmd ';' }
               'main' '=' cmd

      exp  ::= integer | ident
             | exp '-' exp                          (* sub, infix *)
             | exp '*' exp                          (* mul, infix *)
             | ident '(' [ exp { ',' exp } ] ')'    (* call or prefix primitive *)
             | Ctor  '(' [ exp { ',' exp } ] ')'    (* constructor *)
             | '(' exp ')'

      cmd  ::= 'return' exp
             | 'let' ident '=' exp 'in' cmd
             | 'match' exp 'with' { '|' pat '->' cmd } 'end'

      pat  ::= Ctor '(' [ ident { ',' ident } ] ')'
    v}

    The surface is the paper's grammar in {b relaxed A-normal form}: expressions
    nest freely ([(a - b) * c], [Cons(20 - 2, Nil())], [return Nil()] all parse),
    and only {b function calls} are ANF-let-bound, into a labeled
    {!S_syntax.LetCall}. STAR binds tighter than MINUS; the infix [a - b] and
    [a * b] build [EPrim ("sub", …)] / [EPrim ("mul", …)], as do the prefix forms
    the paper writes, and [iszero(a)] is the unary primitive.

    Heads are classified by case. A capitalized head ([Cons], [Nil], [True]) is a
    constructor and builds an {!S_syntax.exp.ETag} carrying its allocation-site
    label; a lowercase head builds an {!S_syntax.exp.EPrim}, which is rewritten
    to a {!S_syntax.LetCall} when it heads a let right-hand side and names a
    declared function. A call anywhere else (e.g. [return dbl(a)], or as an
    operand) parses leniently as an [EPrim] and is stuck at runtime, as is an
    unrecognized primitive. Malformed input raises {!Parse_error}. *)

(** Raised on malformed input. (Defined in {!S_syntax} so the generated lexer and
    grammar can raise it; re-exported here under the public name.) *)
exception Parse_error = S_syntax.Parse_error

(* Run the grammar entry [start] over [src], translating ocamlyacc's failures
   into {!Parse_error}. *)
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

(** Parse S surface text into the labeled {!S_syntax} core program. *)
let parse (src : string) : S_syntax.program = run_parser S_grammar.program src

(** Parse a single S surface command (no definitions, no [main =] header) into a
    one-command-entry program with no functions; a call [f(...)] in it is
    therefore treated as a primitive. Convenient for tests. *)
let parse_cmd_program (src : string) : S_syntax.program =
  run_parser S_grammar.cmd_only src
