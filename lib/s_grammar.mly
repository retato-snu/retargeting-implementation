/* ocamlyacc grammar for the source language S (relaxed A-normal form). */

%{
let next_label = ref 0
let accum : (Label.t * (unit -> S_syntax.cmd)) list ref = ref []
let fun_names : string list ref = ref []

let reset () =
  next_label := 0;
  accum := [];
  fun_names := []

let fresh () : Label.t =
  let l = !next_label in
  next_label := l + 1;
  l

let emit (thunk : unit -> S_syntax.cmd) : Label.t =
  let l = fresh () in
  accum := (l, thunk) :: !accum;
  l

let declare_fun (name : string) : unit = fun_names := name :: !fun_names

let is_declared_fun (name : string) : bool = List.mem name !fun_names

(* Classify rhs at force-time: a declared-function head becomes a LetCall. *)
let let_binder (rhs : S_syntax.exp) (x : string) (k : Label.t) : S_syntax.cmd =
  match rhs with
  | S_syntax.EPrim (h, args) when is_declared_fun h -> S_syntax.LetCall (x, h, args, k)
  | _ -> S_syntax.Let (x, rhs, k)

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

/* STAR binds tighter than MINUS; both left-associative. */
%left MINUS
%left STAR

%start program
%start cmd_only
%type <S_syntax.program> program
%type <S_syntax.program> cmd_only

%%

/* Empty marker reduces first, resetting per-parse state before each parse. */
start_marker:
  | /* empty */ { reset () }

program:
  | start_marker fundefs MAIN EQUALS cmd EOF
      { { S_syntax.funs = $2; ctrl = ctrl_of_accum (); main = $5 } }

fundefs:
  | /* empty */ { [] }
  | fundef fundefs { $1 :: $2 }

fundef:
  | DEF IDENT LPAREN params RPAREN EQUALS cmd SEMI
      { declare_fun $2; { S_syntax.name = $2; params = $4; entry = $7 } }

params:
  | /* empty */ { [] }
  | param_list { $1 }

param_list:
  | IDENT { [ $1 ] }
  | IDENT COMMA param_list { $1 :: $3 }

/* let: the body reduces first under LR, so its entry label is the continuation. */
cmd:
  | RETURN exp { let e = $2 in emit (fun () -> S_syntax.Return e) }
  | LET IDENT EQUALS exp IN cmd
      { let rhs = $4 and x = $2 and k = $6 in
        emit (fun () -> let_binder rhs x k) }
  | MATCH exp WITH branches END
      { let e = $2 and bs = $4 in
        emit (fun () -> S_syntax.Match (e, bs)) }

branches:
  | /* empty */ { [] }
  | BAR pat ARROW cmd branches { ($2, $4) :: $5 }

pat:
  | CTOR LPAREN binders RPAREN { S_syntax.PTag ($1, $3) }

binders:
  | /* empty */ { [] }
  | binder_list { $1 }

binder_list:
  | IDENT { [ $1 ] }
  | IDENT COMMA binder_list { $1 :: $3 }

exp:
  | INT { S_syntax.EInt $1 }
  | IDENT { S_syntax.EVar $1 }
  | exp MINUS exp { S_syntax.EPrim ("sub", [ $1; $3 ]) }
  | exp STAR exp { S_syntax.EPrim ("mul", [ $1; $3 ]) }
  | IDENT LPAREN exp_args RPAREN { S_syntax.EPrim ($1, $3) }
  | CTOR LPAREN exp_args RPAREN { S_syntax.ETag (fresh (), $1, $3) }
  | LPAREN exp RPAREN { $2 }

exp_args:
  | /* empty */ { [] }
  | exp_arg_list { $1 }

exp_arg_list:
  | exp { [ $1 ] }
  | exp COMMA exp_arg_list { $1 :: $3 }

cmd_only:
  | start_marker cmd EOF
      { { S_syntax.funs = []; ctrl = ctrl_of_accum (); main = $2 } }
