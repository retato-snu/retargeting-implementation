/* ocamlyacc grammar for the source language S (strict A-normal form).

   This grammar builds the strict-ANF S_syntax core IR DIRECTLY: there is no
   separate surface AST and no normalization pass. The surface is already in the
   core's shape — every operand is an atom (an integer literal or a variable),
   the only place an application may appear is the right-hand side of a 'let',
   binary primitives are written infix (a - b, a * b), and the head primitive set
   is fixed (sub / mul / iszero) — so the grammar can assign every label and
   build the label -> command control map itself.

   How it builds the core:

   - A module-local fresh-label counter and a control-map accumulator (both refs,
     reset by S_parser before each parse) let the actions allocate labels and
     record commands. 'emit' allocates a fresh label, records a command thunk at
     it, and returns the label.

   - Each 'cmd' reduces to its ENTRY Label.t (the label control reaches first to
     run it), emitting its command(s) into the accumulator as a side effect.
     Because the surface is ANF, each command emits exactly one core command.

   - In 'let x = rhs in body', the body 'cmd' reduces first under LR, so its entry
     label is available as the continuation when the binding command is emitted.

   - A let right-hand side reduces to a binding-builder
     (var -> continuation-label -> cmd). The head of an application is classified
     only when the builder is forced at program-assembly time, by which point the
     full set of declared function names is known — so a forward reference (a call
     to a function defined later in the same mutually-recursive program) is still
     classified as a call, not a primitive. A capitalized head is a constructor
     (LetTag); a lowercase head naming a declared function is a call (LetCall);
     any other lowercase head, and the infix '-'/'*' operators, are primitives
     (Prim with names "sub"/"mul"; "iszero" is the unary primitive form).

   Because operands are atoms only, a nested application (e.g. (10 - 4) * 3 with a
   parenthesized operand, f(g(z)), Cons(sub(20, 2), Nil())) cannot be built by
   this grammar at all, so it is a parse error rather than something silently
   normalized. */

%{
(* A binding-builder: given the bound variable and the continuation label, it
   produces the core command for a 'let x = rhs in <k>'. Classification of an
   application head (constructor / call / primitive) happens when this is forced,
   so the full set of declared function names is already known. *)
type binder = string -> Label.t -> S_syntax.cmd

(* Per-parse mutable state, reset by S_parser before each parse via [reset].
   - [next_label] hands out fresh labels.
   - [accum] collects (label, command-thunk) pairs for the control map; the
     thunks are forced at program assembly, once [fun_names] is complete.
   - [fun_names] is the set of declared function names, accumulated as 'fundef's
     reduce; it tells a call apart from a primitive. *)
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

let is_upper_head (head : string) : bool =
  String.length head > 0 && head.[0] >= 'A' && head.[0] <= 'Z'

let is_declared_fun (name : string) : bool = List.mem name !fun_names

(* Build the binding-builder for an application 'h(atoms)'. The classification is
   deferred into the returned closure so it sees the complete [fun_names]. *)
let app_binder (head : string) (atoms : S_syntax.atom list) : binder =
 fun x k ->
  if is_upper_head head then S_syntax.LetTag (x, head, atoms, k)
  else if is_declared_fun head then S_syntax.LetCall (x, head, atoms, k)
  else S_syntax.Let (x, S_syntax.Prim (head, atoms), k)

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
%token LPAREN RPAREN COMMA BAR ARROW EQUALS SEMI MINUS STAR EOF

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
   accumulator. 'return' takes an atom; the only application site is a 'let' RHS;
   the 'match' scrutinee is an identifier (already an atom).

   For 'let x = rhs in body', the body reduces first under LR, so $6 is the
   continuation label; the binding-builder $4 is applied to the bound name and
   that continuation to emit the binding command. */
cmd:
  | RETURN atom { emit (fun () -> S_syntax.Return $2) }
  | LET IDENT EQUALS rhs IN cmd { emit (fun () -> $4 $2 $6) }
  | MATCH IDENT WITH branches END
      { emit (fun () -> S_syntax.Match (S_syntax.AVar $2, $4)) }

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

/* An atom is the only operand form: an integer literal or a variable. */
atom:
  | INT { S_syntax.AInt $1 }
  | IDENT { S_syntax.AVar $1 }

/* A let right-hand side, as a binding-builder (bound-var -> continuation -> cmd):
     - 'atom - atom'  -> Prim ("sub", [a; b])
     - 'atom * atom'  -> Prim ("mul", [a; b])
     - 'ident(atoms)' -> classified later as call or primitive (e.g. iszero)
     - 'Ctor(atoms)'  -> constructor allocation (LetTag)
     - bare 'atom'    -> Let (x, Atom a, k)
   Operands are atoms only (strict ANF); a parenthesized or nested operand is a
   parse error. */
rhs:
  | atom MINUS atom
      { let a = $1 and b = $3 in
        fun x k -> S_syntax.Let (x, S_syntax.Prim ("sub", [ a; b ]), k) }
  | atom STAR atom
      { let a = $1 and b = $3 in
        fun x k -> S_syntax.Let (x, S_syntax.Prim ("mul", [ a; b ]), k) }
  | IDENT LPAREN args RPAREN { app_binder $1 $3 }
  | CTOR LPAREN args RPAREN { app_binder $1 $3 }
  | atom { let a = $1 in fun x k -> S_syntax.Let (x, S_syntax.Atom a, k) }

/* A possibly-empty, comma-separated list of atom arguments. */
args:
  | /* empty */ { [] }
  | arg_list { $1 }

arg_list:
  | atom { [ $1 ] }
  | atom COMMA arg_list { $1 :: $3 }

/* Entry point for parsing a single command (no definitions, no 'main ='). With
   no functions declared, every lowercase application head is a primitive. The
   command's entry label is the program's main entry. The leading marker resets
   the per-parse state. */
cmd_only:
  | start_marker cmd EOF
      { { S_syntax.funs = []; ctrl = ctrl_of_accum (); main = $2 } }
