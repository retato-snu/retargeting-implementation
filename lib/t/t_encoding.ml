(** The target language T: its abstract syntax, the encoding of T entities into S
    values, and the decoders that recover T from S values.

    T is the language whose abstract machine is calculated from an S-coded
    definitional interpreter, and that interpreter represents T syntax,
    definition tables and environments as ordinary S constructor values
    ({!S_cek.value}, i.e. [VInt] / [VTag]). This module holds the OCaml T
    abstract syntax and the two halves of the syntactic correspondence: the
    {b encoding} [T -> S_cek.value], building a T expression / value / definition
    table / environment as an S value, and its inverse, the {b decoding}
    [⌊·⌋ : S_cek.value -> T], which is defined on every well-formed S value and
    raises {!Decode_error} on a malformed one. (The T continuation frames and
    step relation live in {!T_machine}; decoding needs neither.)

    A T variable is identified by an integer variable id and a T function by an
    integer function id — those integers {e are} T's surface names [x] / [f]. A
    variable {e occurrence} additionally carries its program label and is encoded
    as [Var(label, xid)], whereas a variable used as a {e binder} (a [Let]'s
    bound variable, an environment key) and a function reference decode to the
    bare integer, discarding any label: the paper's [⌊·⌋_var] and [⌊·⌋_fun]
    projections. The T abstract syntax mirrors this. *)

(** {1 Identifiers} *)

type var_id = int
type fun_id = int

(** {1 T abstract syntax} *)

(** T expressions. Each form carries the program label of its root, matching the
    labeled grammar [ℓ:n], [ℓ:x], [ℓ:(e + e)], [ℓ:(e - e)], [ℓ:(e × e)],
    [ℓ:let x = e in e], [ℓ:f(e)] and [ℓ:ifz e then e else e]. *)
type expr =
  | Int of Label.t * int  (** [ℓ:n] — a labeled integer literal *)
  | Var of Label.t * var_id  (** [ℓ:x] — a labeled variable occurrence *)
  | Add of Label.t * expr * expr  (** [ℓ:(e1 + e2)] — addition *)
  | Sub of Label.t * expr * expr  (** [ℓ:(e1 - e2)] — subtraction *)
  | Mul of Label.t * expr * expr  (** [ℓ:(e1 × e2)] — multiplication *)
  | Div of Label.t * expr * expr
      (** [ℓ:(e1 / e2)] — truncate-toward-zero division; [div(_, 0) = 0] *)
  | Mod of Label.t * expr * expr
      (** [ℓ:(e1 % e2)] — remainder [a - b*div(a,b)]; [mod(_, 0) = 0] *)
  | Lt of Label.t * expr * expr
      (** [ℓ:(e1 < e2)] — comparison, the integer [1] if [e1 < e2] else [0] *)
  | Let of Label.t * var_id * expr * expr  (** [ℓ:let x = e1 in e2] *)
  | App of Label.t * fun_id * expr  (** [ℓ:f(e)] *)
  | App2 of Label.t * fun_id * expr * expr
      (** [ℓ:f(e1, e2)] — the callee's params are the ids [0]/[1] *)
  | App3 of Label.t * fun_id * expr * expr * expr
      (** [ℓ:f(e1, e2, e3)] — params are the ids [0]/[1]/[2] *)
  | Ifz of Label.t * expr * expr * expr  (** [ℓ:ifz e0 then e1 else e2] *)

(** {1 T runtime values and environments} *)

(** A T runtime value: T evaluation produces integers only. *)
type value = int

(** A T environment, from variable id to value, most recently bound first. It is
    an association list rather than a map so that encode/decode is a faithful
    inverse of the [Extend]/[Empty] cons-list encoding. *)
type env = (var_id * value) list

(** A T definition table, from function id to body, in the order of the encoded
    [Fun]/[Eof] spine. Formal parameters are implicit: the paper fixes the single
    parameter's id to [0]. *)
type defs = (fun_id * expr) list

(** A T program: a definition table followed by the main expression, matching
    [P ::= f(x) = e; … ; e]. *)
type program = { defs : defs; main : expr }

(** {1 Encoding tags}

    The constructor tags representing T entities as S values — the plain-int ADTs
    of the paper's domain-disambiguation construction:

    {[ defs ::= Fun(int, exp, defs) | Eof()
       env  ::= Extend(int, int, env) | Empty()
       exp  ::= Var(int, int) | Int(int, int)
              | Add(int, exp, exp) | Sub(int, exp, exp)
              | Mul(int, exp, exp) | Let(int, int, exp, exp)
              | App(int, int, exp) | Ifz(int, exp, exp, exp) ]}

    with [Div]/[Mod]/[Lt] shaped like [Sub] and [App2]/[App3] like [App] with
    further operands. T-variables, T-functions and T-labels are {e plain}
    S-integers ([Var = Fun = Lab = Int]), so [fundef] and [lookup] compare
    integer keys directly, with no [Var(l,x)] / [Fun(f)] wrapper nodes. Every
    non-nullary tag stores its identifying T-entity in its {e first} argument —
    the key position the disambiguated domain's partition symbols route on — and
    the distinct nullary tags [Eof] and [Empty] keep [defs] and [env]
    tag-disjoint. *)

let tag_int = "Int"
let tag_var = "Var"
let tag_add = "Add"
let tag_sub = "Sub"
let tag_mul = "Mul"
let tag_div = "Div"
let tag_mod = "Mod"
let tag_lt = "Lt"
let tag_let = "Let"
let tag_app = "App"
let tag_app2 = "App2"
let tag_app3 = "App3"
let tag_ifz = "Ifz"

let tag_fun = "Fun"
let tag_eof = "Eof"
let tag_extend = "Extend"
let tag_empty = "Empty"
let tag_prog = "Prog"

(** {1 Encoding: T -> S value} *)

(** A label is encoded as the S integer underlying it. *)
let enc_label (l : Label.t) : S_cek.value = S_cek.VInt l

(** Encode a T expression: every form is its tag applied to its label followed by
    its operands; binder and callee ids are plain integers. *)
let rec enc_expr (e : expr) : S_cek.value =
  match e with
  | Int (l, n) -> S_cek.VTag (tag_int, [ enc_label l; S_cek.VInt n ])
  | Var (l, x) -> S_cek.VTag (tag_var, [ enc_label l; S_cek.VInt x ])
  | Add (l, e1, e2) ->
      S_cek.VTag (tag_add, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Sub (l, e1, e2) ->
      S_cek.VTag (tag_sub, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Mul (l, e1, e2) ->
      S_cek.VTag (tag_mul, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Div (l, e1, e2) ->
      S_cek.VTag (tag_div, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Mod (l, e1, e2) ->
      S_cek.VTag (tag_mod, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Lt (l, e1, e2) ->
      S_cek.VTag (tag_lt, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Let (l, x, e1, e2) ->
      S_cek.VTag
        (tag_let, [ enc_label l; S_cek.VInt x; enc_expr e1; enc_expr e2 ])
  | App (l, f, e1) ->
      S_cek.VTag (tag_app, [ enc_label l; S_cek.VInt f; enc_expr e1 ])
  | App2 (l, f, e1, e2) ->
      S_cek.VTag
        (tag_app2, [ enc_label l; S_cek.VInt f; enc_expr e1; enc_expr e2 ])
  | App3 (l, f, e1, e2, e3) ->
      S_cek.VTag
        ( tag_app3,
          [ enc_label l; S_cek.VInt f; enc_expr e1; enc_expr e2; enc_expr e3 ] )
  | Ifz (l, e0, e1, e2) ->
      S_cek.VTag
        (tag_ifz, [ enc_label l; enc_expr e0; enc_expr e1; enc_expr e2 ])

(** Encode a definition table as the cons list [Fun(f, body, rest)], keyed by the
    function name and terminated by [Eof()]. *)
let rec enc_defs (ds : defs) : S_cek.value =
  match ds with
  | [] -> S_cek.VTag (tag_eof, [])
  | (f, body) :: rest ->
      S_cek.VTag (tag_fun, [ S_cek.VInt f; enc_expr body; enc_defs rest ])

(** Encode an environment as the cons list [Extend(x, n, rest)], keyed by the
    binder and terminated by [Empty()]. *)
let rec enc_env (rho : env) : S_cek.value =
  match rho with
  | [] -> S_cek.VTag (tag_empty, [])
  | (x, n) :: rest ->
      S_cek.VTag (tag_extend, [ S_cek.VInt x; S_cek.VInt n; enc_env rest ])

(** Encode a whole T program as [Prog(defs, main)]. *)
let enc_program (p : program) : S_cek.value =
  S_cek.VTag (tag_prog, [ enc_defs p.defs; enc_expr p.main ])

(** A T value is an integer, encoded as the S integer. *)
let enc_value (n : value) : S_cek.value = S_cek.VInt n

(** {1 Labeled sub-expressions}

    The T-expression nodes of a program keyed by their labels: the domain [Lab_P]
    of the paper's per-label expression blocks [S^exp_ℓt], with the unique node
    each label keys. Used by the exact instance arm's environment pin
    [env(⟨ℓ,ℓ_t⟩) = \[e ↦ {S^exp_ℓt}·G_max\]], where the abstraction of the node
    at [ℓ_t] is the best abstraction of that block's inhabitants. *)

(** The label of an expression node. *)
let label_of_expr : expr -> Label.t = function
  | Int (l, _)
  | Var (l, _)
  | Add (l, _, _)
  | Sub (l, _, _)
  | Mul (l, _, _)
  | Div (l, _, _)
  | Mod (l, _, _)
  | Lt (l, _, _)
  | Let (l, _, _, _)
  | App (l, _, _)
  | App2 (l, _, _, _)
  | App3 (l, _, _, _, _)
  | Ifz (l, _, _, _) ->
      l

(** Every labeled expression node of a program — the sub-expressions of each
    function body and of [main] — with its label. Labels are unique in a parsed
    program, so this is one node per label. *)
let labeled_sub_exprs (p : program) : (Label.t * expr) list =
  let rec go (acc : (Label.t * expr) list) (e : expr) : (Label.t * expr) list =
    let acc = (label_of_expr e, e) :: acc in
    match e with
    | Int _ | Var _ -> acc
    | Add (_, e1, e2) | Sub (_, e1, e2) | Mul (_, e1, e2) -> go (go acc e1) e2
    | Div (_, e1, e2) | Mod (_, e1, e2) | Lt (_, e1, e2) -> go (go acc e1) e2
    | Let (_, _, e1, e2) -> go (go acc e1) e2
    | App (_, _, e1) -> go acc e1
    | App2 (_, _, e1, e2) -> go (go acc e1) e2
    | App3 (_, _, e1, e2, e3) -> go (go (go acc e1) e2) e3
    | Ifz (_, e0, e1, e2) -> go (go (go acc e0) e1) e2
  in
  let acc = List.fold_left (fun acc (_, body) -> go acc body) [] p.defs in
  go acc p.main

(** {1 Decoding: ⌊·⌋ : S value -> T} *)

(** Raised when an S value does not encode a well-formed T entity in the position
    being decoded; the message names the position and the offending shape. *)
exception Decode_error of string

let decode_error fmt = Printf.ksprintf (fun s -> raise (Decode_error s)) fmt

(** Require an S integer, e.g. for a label or an encoded T value. *)
let dec_int (ctx : string) (v : S_cek.value) : int =
  match v with
  | S_cek.VInt n -> n
  | S_cek.VTag (t, _) -> decode_error "%s: expected an integer, got tag %s" ctx t

let dec_label (ctx : string) (v : S_cek.value) : Label.t = dec_int ctx v

(** A binder/key id is a plain S integer: under the plain-int ADTs [⌊·⌋_var] and
    [⌊·⌋_fun] are the identity on the underlying integer. *)
let dec_var_id (ctx : string) (v : S_cek.value) : var_id =
  dec_int (ctx ^ " variable id") v

let dec_fun_id (ctx : string) (v : S_cek.value) : fun_id =
  dec_int (ctx ^ " function id") v

(** Decode an S value to a T expression ([⌊·⌋] on syntax). *)
let rec dec_expr (v : S_cek.value) : expr =
  match v with
  | S_cek.VInt n -> decode_error "T expression: expected a tag, got integer %d" n
  | S_cek.VTag (t, args) -> (
      match (t, args) with
      | _ when String.equal t tag_int -> (
          match args with
          | [ l; n ] -> Int (dec_label "Int" l, dec_int "Int payload" n)
          | _ -> arity_error tag_int args)
      | _ when String.equal t tag_var -> (
          match args with
          | [ l; x ] -> Var (dec_label "Var" l, dec_int "Var id" x)
          | _ -> arity_error tag_var args)
      | _ when String.equal t tag_add -> (
          match args with
          | [ l; e1; e2 ] ->
              Add (dec_label "Add" l, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_add args)
      | _ when String.equal t tag_sub -> (
          match args with
          | [ l; e1; e2 ] ->
              Sub (dec_label "Sub" l, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_sub args)
      | _ when String.equal t tag_mul -> (
          match args with
          | [ l; e1; e2 ] ->
              Mul (dec_label "Mul" l, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_mul args)
      | _ when String.equal t tag_div -> (
          match args with
          | [ l; e1; e2 ] ->
              Div (dec_label "Div" l, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_div args)
      | _ when String.equal t tag_mod -> (
          match args with
          | [ l; e1; e2 ] ->
              Mod (dec_label "Mod" l, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_mod args)
      | _ when String.equal t tag_lt -> (
          match args with
          | [ l; e1; e2 ] ->
              Lt (dec_label "Lt" l, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_lt args)
      | _ when String.equal t tag_let -> (
          match args with
          | [ l; x; e1; e2 ] ->
              Let
                ( dec_label "Let" l,
                  dec_var_id "Let binder" x,
                  dec_expr e1,
                  dec_expr e2 )
          | _ -> arity_error tag_let args)
      | _ when String.equal t tag_app -> (
          match args with
          | [ l; f; e1 ] ->
              App (dec_label "App" l, dec_fun_id "App callee" f, dec_expr e1)
          | _ -> arity_error tag_app args)
      | _ when String.equal t tag_app2 -> (
          match args with
          | [ l; f; e1; e2 ] ->
              App2
                ( dec_label "App2" l,
                  dec_fun_id "App2 callee" f,
                  dec_expr e1,
                  dec_expr e2 )
          | _ -> arity_error tag_app2 args)
      | _ when String.equal t tag_app3 -> (
          match args with
          | [ l; f; e1; e2; e3 ] ->
              App3
                ( dec_label "App3" l,
                  dec_fun_id "App3 callee" f,
                  dec_expr e1,
                  dec_expr e2,
                  dec_expr e3 )
          | _ -> arity_error tag_app3 args)
      | _ when String.equal t tag_ifz -> (
          match args with
          | [ l; e0; e1; e2 ] ->
              Ifz (dec_label "Ifz" l, dec_expr e0, dec_expr e1, dec_expr e2)
          | _ -> arity_error tag_ifz args)
      | _ ->
          decode_error "T expression: unexpected tag %s/%d" t
            (List.length args))

and arity_error tag args =
  decode_error "T expression: malformed %s/%d" tag (List.length args)

(** Decode a T definition table ([⌊·⌋] on the [Fun]/[Eof] spine). *)
let rec dec_defs (v : S_cek.value) : defs =
  match v with
  | S_cek.VTag (t, []) when String.equal t tag_eof -> []
  | S_cek.VTag (t, [ f; body; rest ]) when String.equal t tag_fun ->
      (dec_fun_id "Fun entry" f, dec_expr body) :: dec_defs rest
  | S_cek.VTag (t, args) ->
      decode_error "T defs: unexpected tag %s/%d" t (List.length args)
  | S_cek.VInt n -> decode_error "T defs: expected a tag, got integer %d" n

(** Decode a T environment ([⌊·⌋] on the [Extend]/[Empty] spine). *)
let rec dec_env (v : S_cek.value) : env =
  match v with
  | S_cek.VTag (t, []) when String.equal t tag_empty -> []
  | S_cek.VTag (t, [ x; n; rest ]) when String.equal t tag_extend ->
      (dec_var_id "Extend key" x, dec_int "Extend value" n) :: dec_env rest
  | S_cek.VTag (t, args) ->
      decode_error "T env: unexpected tag %s/%d" t (List.length args)
  | S_cek.VInt n -> decode_error "T env: expected a tag, got integer %d" n

(** Decode a whole T program ([⌊·⌋] on [Prog(defs, main)]). *)
let dec_program (v : S_cek.value) : program =
  match v with
  | S_cek.VTag (t, [ ds; main ]) when String.equal t tag_prog ->
      { defs = dec_defs ds; main = dec_expr main }
  | _ -> decode_error "T program: expected %s(defs, main)" tag_prog

(** Decode a T value (an integer). *)
let dec_value (v : S_cek.value) : value = dec_int "T value" v
