/* ocamlyacc grammar for the source language S (the paper's relaxed A-normal form).

   This grammar builds the S_syntax core IR DIRECTLY: there is no separate
   surface AST and no normalization pass. The surface is the paper's grammar: an
   expression 'e' is an integer literal, a variable, a primitive application
   (infix 'a + b' / 'a - b' / 'a * b' / 'a == b', or prefix 'iszero(e)' /
   'sub(...)' / 'mul(...)'), or a constructor application 'T(e...)'. Primitive
   and constructor operands are themselves expressions and nest freely (relaxed
   ANF) — '(10 - 4) * 3', 'Cons(20 - 2, Nil())', etc. all parse. Only function
   CALLS are ANF-let-bound; they get their own labeled command (LetCall).

   How it builds the core:

   - A module-local fresh-label counter and a control-map accumulator (both refs,
     reset by S_parser before each parse) let the actions allocate labels and
     record commands. 'emit' allocates a fresh label, records a command thunk at
     it, and returns the label. Constructor expressions ('ETag') also draw a
     fresh label as their ALLOCATION SITE, from the same fresh-counter namespace.

   - Each 'cmd' reduces to its ENTRY Label.t (the label control reaches first to
     run it), emitting its command(s) into the accumulator as a side effect.

   - In 'let x = rhs in body', the body 'cmd' reduces first under LR, so its entry
     label is available as the continuation when the binding command is emitted.

   - A let right-hand side is parsed as an 'exp', then classified at force-time
     (program-assembly time, when the full set of declared function names is
     known): if the rhs is 'EPrim(h, args)' with 'h' a DECLARED FUNCTION, it is
     rewritten to 'LetCall(x, h, args, k)'; otherwise it is 'Let(x, rhs, k)' (a
     constructor rhs is already an 'ETag', so it is just a 'Let'). The deferral
     means a forward reference (a call to a function defined later in the same
     mutually-recursive program) is still classified as a call. */

%{
(* Per-parse mutable state, reset by S_parser before each parse via [reset].
   - [next_label] hands out fresh labels (for both command labels and ETag
     allocation sites).
   - [accum] collects (label, command-thunk) pairs for the control map; the
     thunks are forced at program assembly, once [fun_names] is complete.
   - [fun_names] is the set of declared function names, accumulated as 'fundef's
     reduce; it tells a call apart from a primitive at force-time. *)
let next_label = ref 0
let accum : (Label.t * (unit -> S_syntax.cmd)) list ref = ref []
let fun_names : string list ref = ref []

(* Reset the per-parse state. Called by S_parser before running an entry. *)
let reset () =
  next_label := 0;
  accum := [];
  fun_names := []

(* Allocate a fresh label. *)
let fresh () : Label.t =
  let l = !next_label in
  next_label := l + 1;
  l

(* Record a command (as a thunk) at a fresh label and return that label. The
   thunk is forced at program assembly, when [fun_names] is fully populated. *)
let emit (thunk : unit -> S_syntax.cmd) : Label.t =
  let l = fresh () in
  accum := (l, thunk) :: !accum;
  l

(* Note a declared function name so later (and earlier, mutually-recursive)
   bodies classify a call to it as a LetCall rather than a primitive. *)
let declare_fun (name : string) : unit = fun_names := name :: !fun_names

let is_declared_fun (name : string) : bool = List.mem name !fun_names

(* Classify a let right-hand side at force-time. A constructor expression is an
   ETag already, so it is just a Let; a primitive application whose head names a
   declared function is a call (LetCall); everything else is a Let over the
   expression. *)
let let_binder (rhs : S_syntax.exp) (x : string) (k : Label.t) : S_syntax.cmd =
  match rhs with
  | S_syntax.EPrim (h, args) when is_declared_fun h -> S_syntax.LetCall (x, h, args, k)
  | _ -> S_syntax.Let (x, rhs, k)

(* Force every accumulated command thunk into the label -> command control map.
   Called at program assembly, when [fun_names] is complete. *)
let ctrl_of_accum () : S_syntax.cmd Label.Map.t =
  List.fold_left
    (fun m (l, thunk) -> Label.Map.add l (thunk ()) m)
    Label.Map.empty !accum
%}

%token <int> INT
%token <string> IDENT
%token <string> CTOR
%token LET IN MATCH WITH END RETURN DEF MAIN
%token LPAREN RPAREN COMMA BAR ARROW EQUALS SEMI PLUS MINUS STAR EQEQ EOF

/* Operator precedence for the nested infix primitives, loosest to tightest:
   equality '==', then the additive '+' / '-', then '*'. So 'a - b * c' parses as
   'a - (b * c)' and 'a - b == c' as '(a - b) == c'. All left-associative. */
%left EQEQ
%left PLUS MINUS
%left STAR

%start program
%start cmd_only
%type <S_syntax.program> program
%type <S_syntax.program> cmd_only

%%

/* An empty marker that reduces first (before any token is shifted), so the
   per-parse mutable state is reset at the start of every parse without needing an
   externally-callable reset (the generated grammar interface exports only tokens
   and start symbols, not header values). */
start_marker:
  | /* empty */ { reset () }

/* A program: zero or more definitions then 'main = cmd'. The function names are
   recorded as the 'fundef's reduce, so by the time this rule reduces the call /
   primitive classification (deferred into the accumulated thunks) is complete. */
program:
  | start_marker fundefs MAIN EQUALS cmd EOF
      { { S_syntax.funs = $2; ctrl = ctrl_of_accum (); main = $5 } }

/* A possibly-empty run of definitions, in source order. */
fundefs:
  | /* empty */ { [] }
  | fundef fundefs { $1 :: $2 }

/* A function definition. Its name is declared for call classification; since the
   accumulated binding thunks are forced only at program assembly (after every
   'fundef' has reduced), declaring it here suffices even for a self-recursive or
   forward call. The entry is the body's entry label. */
fundef:
  | DEF IDENT LPAREN params RPAREN EQUALS cmd SEMI
      { declare_fun $2; { S_syntax.name = $2; params = $4; entry = $7 } }

/* A possibly-empty, comma-separated list of parameter binders. */
params:
  | /* empty */ { [] }
  | param_list { $1 }

param_list:
  | IDENT { [ $1 ] }
  | IDENT COMMA param_list { $1 :: $3 }

/* Commands. Each reduces to its ENTRY Label.t, emitting its command(s) into the
   accumulator. 'return' takes an expression; the 'match' scrutinee is an
   expression; a 'let' right-hand side is an expression, classified into a Let or
   a LetCall when the binder thunk is forced.

   For 'let x = rhs in body', the body reduces first under LR, so $6 is the
   continuation label; the binder is built from the rhs expression, the bound
   name, and that continuation. */
cmd:
  | RETURN exp { let e = $2 in emit (fun () -> S_syntax.Return e) }
  | LET IDENT EQUALS exp IN cmd
      { let rhs = $4 and x = $2 and k = $6 in
        emit (fun () -> let_binder rhs x k) }
  | MATCH exp WITH branches END
      { let e = $2 and bs = $4 in
        emit (fun () -> S_syntax.Match (e, bs)) }

/* Zero or more '| pat -> cmd' branches, in source order. Each branch body
   reduces to its entry label, paired with the branch pattern. */
branches:
  | /* empty */ { [] }
  | BAR pat ARROW cmd branches { ($2, $4) :: $5 }

/* A pattern is a capitalized constructor applied to a parenthesized list of
   field binders (identifiers), possibly empty. */
pat:
  | CTOR LPAREN binders RPAREN { S_syntax.PTag ($1, $3) }

binders:
  | /* empty */ { [] }
  | binder_list { $1 }

binder_list:
  | IDENT { [ $1 ] }
  | IDENT COMMA binder_list { $1 :: $3 }

/* An expression: integer literal, variable, infix or prefix primitive, or a
   constructor application. Operands nest freely (relaxed ANF).
     - 'n'             -> EInt
     - 'x'             -> EVar
     - 'e + e'         -> EPrim ("add", [a; b])
     - 'e - e'         -> EPrim ("sub", [a; b])
     - 'e * e'         -> EPrim ("mul", [a; b])
     - 'e == e'        -> EPrim ("eq",  [a; b])   (a Boolean tag True()/False())
     - 'ident(e...)'   -> EPrim (name, args)   (prefix prim, e.g. iszero(e); a
                          declared-function head is rewritten to a LetCall only
                          when it heads a let right-hand side)
     - 'Ctor(e...)'    -> ETag (fresh allocation site, tag, args)
     - '(e)'           -> e */
exp:
  | INT { S_syntax.EInt $1 }
  | IDENT { S_syntax.EVar $1 }
  | exp PLUS exp { S_syntax.EPrim ("add", [ $1; $3 ]) }
  | exp MINUS exp { S_syntax.EPrim ("sub", [ $1; $3 ]) }
  | exp STAR exp { S_syntax.EPrim ("mul", [ $1; $3 ]) }
  | exp EQEQ exp { S_syntax.EPrim ("eq", [ $1; $3 ]) }
  | IDENT LPAREN exp_args RPAREN { S_syntax.EPrim ($1, $3) }
  | CTOR LPAREN exp_args RPAREN { S_syntax.ETag (fresh (), $1, $3) }
  | LPAREN exp RPAREN { $2 }

/* A possibly-empty, comma-separated list of expression arguments. */
exp_args:
  | /* empty */ { [] }
  | exp_arg_list { $1 }

exp_arg_list:
  | exp { [ $1 ] }
  | exp COMMA exp_arg_list { $1 :: $3 }

/* Entry point for parsing a single command (no definitions, no 'main ='). With
   no functions declared, every lowercase application head is a primitive. The
   command's entry label is the program's main entry. The leading marker resets
   the per-parse state. */
cmd_only:
  | start_marker cmd EOF
      { { S_syntax.funs = []; ctrl = ctrl_of_accum (); main = $2 } }
