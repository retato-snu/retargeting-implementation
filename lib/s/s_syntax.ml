(** S: the core IR of the source language for which an abstract interpreter
    already exists — mutually-recursive functions, constructors with pattern
    match, integers, and primitives.

    S is in the paper's {b relaxed} A-normal form: only {b function calls} are
    ANF-let-bound and labeled, through {!LetCall}. Primitive applications [o(ē)]
    and constructor allocations [T(ē)] are ordinary {!exp} forms that nest freely
    in any operand position, and expression evaluation ([eval e ρ]) transfers no
    control. An {!ETag} node carries its own {b allocation-site} {!Label.t}
    (parser-assigned in the same fresh-counter namespace as command labels) and
    consumers read the site from the node, never reconstructing it from a command
    label; primitive applications have no allocation site, integers using the
    single ℘(Int) lattice. Pattern match dispatches on constructor tag and arity
    only — there is no wildcard. *)

(** Raised on malformed S surface input. It lives in this shared core-IR module
    so that the generated lexer ({!S_lexer}) and grammar ({!S_grammar}) can both
    raise it (the generated parser's interface exposes only tokens and start
    symbols); {!S_parser} re-exports it under the same name. *)
exception Parse_error of string

type var = string
type tag = string (* constructor / data tag *)
type prim = string (* primitive operator name *)

(** Expressions [e]: an integer literal, a variable, a primitive application
    [o(ē)], or a constructor application [T(ē)] whose label [l] is its allocation
    site. Operands are themselves expressions, so they nest freely. *)
type exp =
  | EInt of int
  | EVar of var
  | EPrim of prim * exp list (* o(ē) *)
  | ETag of Label.t * tag * exp list (* T(ē); the Label.t is the allocation site *)

(** A [Match] pattern: a constructor tag with binders for its fields. *)
type pat = PTag of tag * var list (* K(x1, ..., xn) *)

(** Commands: the labeled control points of S. Each non-tail command names its
    continuation by label, resolved through the program's control map.

    - [Return e]: return the value of [e] (rule [S-Return] / program result).
    - [Let (x, e, l)]: bind [x] to [eval e] and continue at [l] (rule
      [S-LetExp]); this also covers constructor allocation, an [ETag]
      right-hand side.
    - [LetCall (x, f, es, l)]: call [f] on [es], bind its result to [x], and
      continue at [l] (rule [S-LetCall]).
    - [Match (e, branches)]: evaluate the scrutinee to a tagged value, take the
      first branch whose pattern matches its tag and arity, bind the pattern
      variables, and continue at the branch label (rule [S-Match]). *)
type cmd =
  | Return of exp
  | Let of var * exp * Label.t (* let x = e in <label>     [S-LetExp] *)
  | LetCall of var * var * exp list * Label.t (* let x = f(ē) in <label>  [S-LetCall] *)
  | Match of exp * (pat * Label.t) list (* match e with b̄ end       [S-Match] *)

(** A function definition: name, formal parameters, and entry label. *)
type fundef = { name : var; params : var list; entry : Label.t }

(** A program: function definitions, the label -> command control map, and the
    main entry label. *)
type program = {
  funs : fundef list;
  ctrl : cmd Label.Map.t;
  main : Label.t;
}

(** The command at a label, or [invalid_arg] if the control map has no entry. *)
let cmd_at (p : program) (l : Label.t) : cmd =
  match Label.Map.find_opt l p.ctrl with
  | Some c -> c
  | None ->
      invalid_arg
        (Printf.sprintf "S_syntax.cmd_at: no command at %s" (Label.to_string l))

(** Build a control map from [(label, cmd)] pairs. *)
let ctrl_of_list (pairs : (Label.t * cmd) list) : cmd Label.Map.t =
  List.fold_left (fun m (l, c) -> Label.Map.add l c m) Label.Map.empty pairs
