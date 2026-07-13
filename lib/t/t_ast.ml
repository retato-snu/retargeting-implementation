(** The label-less surface AST for the target language T.

    The [ocamlyacc] grammar ({!T_grammar}) builds these types directly in its
    semantic actions; {!T_parser} then runs a labeling pass that resolves names
    to the integer ids {!T_encoding} expects and assigns fresh labels. The
    surface types live in their own module so that both the generated parser and
    the wrapper can refer to them without a dependency cycle. *)

(** Raised on malformed input. Declared here (not in the generated grammar, whose
    interface would not expose it) so the generated lexer can raise it and
    {!T_parser} can re-export it under the same name. *)
exception Parse_error of string

(** A surface expression. Names are kept verbatim as strings; an application head
    and a variable occurrence are told apart syntactically (an identifier
    followed by [(...)] is an application). *)
type sexpr =
  | SInt of int
  | SVar of string
  | SApp of string * sexpr  (** [f(e)] — an application head and its argument *)
  | SApp2 of string * sexpr * sexpr  (** [f(e1, e2)] — arity-2 application *)
  | SApp3 of string * sexpr * sexpr * sexpr  (** [f(e1, e2, e3)] — arity-3 *)
  | SAdd of sexpr * sexpr
  | SSub of sexpr * sexpr
  | SMul of sexpr * sexpr
  | SDiv of sexpr * sexpr  (** [e / e] — truncating division *)
  | SMod of sexpr * sexpr  (** [e % e] — remainder *)
  | SLt of sexpr * sexpr  (** [e < e] — order comparison (0/1) *)
  | SLet of string * sexpr * sexpr
  | SIfz of sexpr * sexpr * sexpr

(** A surface definition: function name, formal parameter names (arity 1–3, left
    to right), and body. The labeling pass maps the parameters to ids [0 .. k-1]. *)
type sdef = { name : string; params : string list; body : sexpr }

(** A surface program: definitions in source order, then the main expression. *)
type sprogram = { defs : sdef list; main : sexpr }
