(** The paper's role map — {b positional domain disambiguation}
    (§"Positional Domain Disambiguation"):

    {[ role : ((Tag × ℕ) ∪ Var ∪ Exp) → Role ]}

    Retargeting needs exact labels to recover \langt-flow sensitivity and exact
    variable/function identifiers to recover environment lookup, but it does
    {e not} need every integer flowing through the interpreter to be exact. The
    same S-integer type plays different semantic roles in different positions of
    the abstract state, so the domain takes the role map as a parameter and picks
    a base domain per role: exact abstract integers for the identifier roles
    ([label], [var], the function-name key), a {e swappable} numeric abstraction
    for [num] (parity, intervals, constants, …; here the graded
    {!Domain_intf.aint}), and role-specific tree grammars for the ADT roles. The
    abstract operators are role-annotated accordingly: the [lookup] key
    comparison is [==_{var,var⇒bool}], the [ifz] zero test [==_{num,num⇒bool}].

    This module is the first-class form of the field-role table that the
    auxiliary-family certificate {!Role_pe} recovers structurally from the
    interpreter text ({!Role_pe.fields_of_tag}); the two must agree tag for tag,
    which the gate suite on the artifact/impl-measure branch checks.
    {!Domain_dis} consumes it. The shared
    {!Domain_intf.DOMAIN} surface is unchanged — the role map is a parameter of
    the disambiguated domain only, so the base and tree-grammar lanes are
    untouched. *)

module T = T_encoding

(** A semantic role: the integer-valued ([Label]/[Var]/[Fname]/[Num]) and
    ADT-valued ([Exp]/[Env]/[Fundef]/[Bool]) roles of the paper's [Role]. *)
type t =
  | Label  (** an AST node label [ℓt] — an exact integer key ([ℤ^ABS_label]) *)
  | Var  (** an environment binder / variable id — an exact key ([ℤ^ABS_var]) *)
  | Fname
      (** a function name / application callee id — the exact key of the
          function-definition table *)
  | Num  (** a T-numeric value — the {e swappable} base domain ([ℤ^ABS_num]) *)
  | Exp  (** a reified T expression (ADT; tree-grammar symbols) *)
  | Env  (** a reified T environment (ADT) *)
  | Fundef  (** a reified T definition table (ADT) *)
  | Bool  (** a reified boolean — the [True]/[False] tree-grammar symbols *)

(** The identifier-key roles: the abstract integer is pinned to the exact
    [α_r{c}] whose concretization is the singleton [{c}], and the disambiguated
    partition routes a construction on the field carrying this role. *)
let is_key : t -> bool = function Label | Var | Fname -> true | _ -> false

(** The numeric role — the one position family whose base domain may be coarsened
    without disturbing the exactness the retargeted partition needs. *)
let is_numeric : t -> bool = function Num -> true | _ -> false

(** The ADT roles — reified objects represented by tree-grammar symbols. *)
let is_adt : t -> bool = function Exp | Env | Fundef | Bool -> true | _ -> false

let to_string : t -> string = function
  | Label -> "label"
  | Var -> "var"
  | Fname -> "fname"
  | Num -> "num"
  | Exp -> "exp"
  | Env -> "env"
  | Fundef -> "fundef"
  | Bool -> "bool"

(** [fields tg] is [role(tg, ·)], the field roles of the encoding tag [tg] — the
    [(Tag × ℕ)] part of the role map, read off {!T_encoding}'s constructor layout
    (an expression node stores its [Label] first; the [Extend]/[Fun] conses their
    [Var]/[Fname] key first). [None] for a tag outside the T encoding (junk
    flows, which the domain routes to a garbage symbol). *)
let fields (tg : S_syntax.tag) : t list option =
  if String.equal tg T.tag_int then Some [ Label; Num ]
  else if String.equal tg T.tag_var then Some [ Label; Var ]
  else if
    String.equal tg T.tag_add || String.equal tg T.tag_sub
    || String.equal tg T.tag_mul || String.equal tg T.tag_div
    || String.equal tg T.tag_mod || String.equal tg T.tag_lt
  then Some [ Label; Exp; Exp ]
  else if String.equal tg T.tag_let then Some [ Label; Var; Exp; Exp ]
  else if String.equal tg T.tag_app then Some [ Label; Fname; Exp ]
  else if String.equal tg T.tag_app2 then Some [ Label; Fname; Exp; Exp ]
  else if String.equal tg T.tag_app3 then Some [ Label; Fname; Exp; Exp; Exp ]
  else if String.equal tg T.tag_ifz then Some [ Label; Exp; Exp; Exp ]
  else if String.equal tg T.tag_fun then Some [ Fname; Exp; Fundef ]
  else if String.equal tg T.tag_eof then Some []
  else if String.equal tg T.tag_extend then Some [ Var; Num; Env ]
  else if String.equal tg T.tag_empty then Some []
  else if String.equal tg T.tag_prog then Some [ Fundef; Exp ]
  else if String.equal tg "True" || String.equal tg "False" then Some []
  else None

(** [field tg i] is [role(tg, i)], the role of the [i]th field of tag [tg], or
    [None] if [tg] is not a T-encoding tag or has no [i]th field. *)
let field (tg : S_syntax.tag) (i : int) : t option =
  match fields tg with Some fs -> List.nth_opt fs i | None -> None
