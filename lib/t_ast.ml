(** The label-less surface AST for the target language T. *)

(** Raised on malformed input. *)
exception Parse_error of string

type sexpr =
  | SInt of int
  | SVar of string
  | SApp of string * sexpr  (** [f(e)] *)
  | SSub of sexpr * sexpr
  | SMul of sexpr * sexpr
  | SLet of string * sexpr * sexpr
  | SIfz of sexpr * sexpr * sexpr

type sdef = { name : string; param : string; body : sexpr }

type sprogram = { defs : sdef list; main : sexpr }
