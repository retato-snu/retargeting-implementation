(** Target language T: abstract syntax, encoding of T entities into S values, and decoders recovering T from S values. *)

type var_id = int

type fun_id = int

type expr =
  | Int of Label.t * int
  | Var of Label.t * var_id
  | Sub of Label.t * expr * expr
  | Mul of Label.t * expr * expr
  | Let of Label.t * var_id * expr * expr
  | App of Label.t * fun_id * expr
  | Ifz of Label.t * expr * expr * expr

type value = int

type env = (var_id * value) list

type defs = (fun_id * expr) list

type program = { defs : defs; main : expr }

let tag_int = "Int"
let tag_var = "Var"
let tag_sub = "Sub"
let tag_mul = "Mul"
let tag_let = "Let"
let tag_app = "App"
let tag_ifz = "Ifz"
let tag_fun = "Fun"
let tag_nil = "Nil"
let tag_env = "Env"
let tag_defs = "Defs"
let tag_prog = "Prog"

(** Placeholder label for a binder's [Var] wrapper; decode drops it, so any value round-trips. *)
let binder_label : Label.t = 0

let enc_label (l : Label.t) : S_cek.value = S_cek.VInt l

let enc_var_id (x : var_id) : S_cek.value =
  S_cek.VTag (tag_var, [ enc_label binder_label; S_cek.VInt x ])

let enc_fun_id (f : fun_id) : S_cek.value = S_cek.VTag (tag_fun, [ S_cek.VInt f ])

let rec enc_expr (e : expr) : S_cek.value =
  match e with
  | Int (l, n) -> S_cek.VTag (tag_int, [ enc_label l; S_cek.VInt n ])
  | Var (l, x) -> S_cek.VTag (tag_var, [ enc_label l; S_cek.VInt x ])
  | Sub (l, e1, e2) ->
      S_cek.VTag (tag_sub, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Mul (l, e1, e2) ->
      S_cek.VTag (tag_mul, [ enc_label l; enc_expr e1; enc_expr e2 ])
  | Let (l, x, e1, e2) ->
      S_cek.VTag
        (tag_let, [ enc_label l; enc_var_id x; enc_expr e1; enc_expr e2 ])
  | App (l, f, e1) ->
      S_cek.VTag (tag_app, [ enc_label l; enc_fun_id f; enc_expr e1 ])
  | Ifz (l, e0, e1, e2) ->
      S_cek.VTag
        (tag_ifz, [ enc_label l; enc_expr e0; enc_expr e1; enc_expr e2 ])

let rec enc_defs (ds : defs) : S_cek.value =
  match ds with
  | [] -> S_cek.VTag (tag_nil, [])
  | (f, body) :: rest ->
      S_cek.VTag (tag_defs, [ enc_fun_id f; enc_expr body; enc_defs rest ])

let rec enc_env (rho : env) : S_cek.value =
  match rho with
  | [] -> S_cek.VTag (tag_nil, [])
  | (x, n) :: rest ->
      S_cek.VTag (tag_env, [ enc_var_id x; S_cek.VInt n; enc_env rest ])

let enc_program (p : program) : S_cek.value =
  S_cek.VTag (tag_prog, [ enc_defs p.defs; enc_expr p.main ])

let enc_value (n : value) : S_cek.value = S_cek.VInt n

exception Decode_error of string

let decode_error fmt = Printf.ksprintf (fun s -> raise (Decode_error s)) fmt

let dec_int (ctx : string) (v : S_cek.value) : int =
  match v with
  | S_cek.VInt n -> n
  | S_cek.VTag (t, _) -> decode_error "%s: expected an integer, got tag %s" ctx t

let dec_label (ctx : string) (v : S_cek.value) : Label.t = dec_int ctx v

let dec_var_id (ctx : string) (v : S_cek.value) : var_id =
  match v with
  | S_cek.VTag (t, [ _label; xid ]) when String.equal t tag_var ->
      dec_int (ctx ^ " variable id") xid
  | _ -> decode_error "%s: expected %s(label, xid)" ctx tag_var

let dec_fun_id (ctx : string) (v : S_cek.value) : fun_id =
  match v with
  | S_cek.VTag (t, [ fid ]) when String.equal t tag_fun ->
      dec_int (ctx ^ " function id") fid
  | _ -> decode_error "%s: expected %s(fid)" ctx tag_fun

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

let rec dec_defs (v : S_cek.value) : defs =
  match v with
  | S_cek.VTag (t, []) when String.equal t tag_nil -> []
  | S_cek.VTag (t, [ f; body; rest ]) when String.equal t tag_defs ->
      (dec_fun_id "Defs entry" f, dec_expr body) :: dec_defs rest
  | S_cek.VTag (t, args) ->
      decode_error "T defs: unexpected tag %s/%d" t (List.length args)
  | S_cek.VInt n -> decode_error "T defs: expected a tag, got integer %d" n

let rec dec_env (v : S_cek.value) : env =
  match v with
  | S_cek.VTag (t, []) when String.equal t tag_nil -> []
  | S_cek.VTag (t, [ x; n; rest ]) when String.equal t tag_env ->
      (dec_var_id "Env key" x, dec_int "Env value" n) :: dec_env rest
  | S_cek.VTag (t, args) ->
      decode_error "T env: unexpected tag %s/%d" t (List.length args)
  | S_cek.VInt n -> decode_error "T env: expected a tag, got integer %d" n

let dec_program (v : S_cek.value) : program =
  match v with
  | S_cek.VTag (t, [ ds; main ]) when String.equal t tag_prog ->
      { defs = dec_defs ds; main = dec_expr main }
  | _ -> decode_error "T program: expected %s(defs, main)" tag_prog

let dec_value (v : S_cek.value) : value = dec_int "T value" v
