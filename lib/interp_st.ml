(** [I_S^T]: the definitional interpreter for the target language T, written as
    an S program (a {!S_syntax.program}).

    This is the central object of the construction: a big-step interpreter for T
    expressed in the relaxed-ANF core S, so that the existing S abstract
    interpreter can be partially evaluated against it to obtain a T abstract
    machine. It pattern-matches on the S-encoded T syntax produced by
    {!T_encoding} (tagged values such as [Int], [Var], [Add], [Sub], [Let],
    [App], [Ifz]), evaluates sub-expressions recursively, and threads a T
    environment and a T definition table. It transcribes the paper's listing
    branch by branch: the recursive [eval], the helpers [lookup] (over the
    encoded environment spine), [fundef] (over the encoded definition spine) and
    [extend] (a non-recursive environment cons), and a [main] that seeds the
    initial environment with the single implicit parameter. The three arms
    [Div]/[Mod]/[Lt] and the arities [App2]/[App3] are the paper's extension of
    the listing; each adds ordinary operator and eval-call boundaries only.

    Rather than building the labeled control map by hand, the interpreter is
    written below as ordinary S surface text and parsed with {!S_parser.parse},
    which maps each command to one labeled core command and hands out fresh
    labels (plus a fresh allocation site per constructor). Those labels are
    arbitrary: the consumers ({!Projection}, {!S_abstract}) read [eval]'s
    branches {e structurally}, by command shape and never by numeric label, so
    re-parsing is transparent. Both the base and the specialized analyzer are
    derived from this one interpreter. *)

(** {1 Encoding tags}

    The S constructor tags the interpreter dispatches on. They must agree
    verbatim with {!T_encoding}, but are repeated here as plain strings so this
    module reads as a self-contained S program. *)

let t_int = "Int"
let t_var = "Var"
let t_add = "Add"
let t_sub = "Sub"
let t_mul = "Mul"
let t_div = "Div"
let t_mod = "Mod"
let t_lt = "Lt"
let t_let = "Let"
let t_app = "App"
let t_app2 = "App2"
let t_app3 = "App3"
let t_ifz = "Ifz"
let t_fun = "Fun"
let t_eof = "Eof"
let t_extend = "Extend"
let t_empty = "Empty"
let t_prog = "Prog"

(* Boolean constructors produced by the equality primitive [==]. *)
let t_true = "True"
let t_false = "False"

(** {1 Function names}

    The paper's five S functions: [eval], [lookup] and [fundef] are recursive and
    reached through a call, [extend] is the non-recursive environment cons. *)

let f_eval = "eval"
let f_lookup = "lookup"
let f_fundef = "fundef"
let f_extend = "extend"

(** {1 Seed variable names}

    [main] reads the encoded T program and its integer argument as free
    variables; the driver binds them in the seed environment. *)

let arg_p = "p"
let arg_arg = "arg"

(** {1 The interpreter source}

    The five S functions and [main] in surface syntax, with the tags, function
    names and seed variable names above spliced in so the source stays in
    lockstep with them. Only function calls are ANF-let-bound; primitives and
    constructors nest freely, so [fid == fid2] is the bare scrutinee of a [match]
    and binary primitives are written infix ([a + b] / [a - b] / [a * b]).

    [fundef(defs, fid)] and [lookup(env, xid)] walk the encoded [Fun]/[Eof] and
    [Extend]/[Empty] spines and return the payload whose key — the cons's first
    argument — equals the sought id, tested with S's equality [==] (which yields
    the [True()] / [False()] the match scrutinizes). [extend] conses one binding.
    Binder and callee ids are plain integers (no [Var]/[Fun] wrapper nodes, no
    inner unwrap matches) and the implicit function parameter is the id [0], so
    [App]/[App2]/[App3] build the callee's environment by extending [Empty()] at
    the ids [0], [1], [2]. [main(p, arg)] destructures [Prog(defs, e)], binds the
    implicit parameter to [arg], and evaluates [e]. *)
let source : string =
  Printf.sprintf
    {source|
def %s(defs, fid) =
  match defs with
  | %s(fid2, body, rest) ->
      match fid == fid2 with
      | %s() -> return body
      | %s() ->
          let r = %s(rest, fid) in
          return r
      end
  end ;

def %s(env, xid) =
  match env with
  | %s(xid2, val, rest) ->
      match xid == xid2 with
      | %s() -> return val
      | %s() ->
          let r = %s(rest, xid) in
          return r
      end
  end ;

def %s(env, x, val) =
  let r = %s(x, val, env) in
  return r ;

def %s(e, env, defs) =
  match e with
  | %s(l, n) ->
      let r = n in
      return r
  | %s(l, xid) ->
      let r = %s(env, xid) in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = v1 + v2 in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = v1 - v2 in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = v1 * v2 in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = div(v1, v2) in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = mod(v1, v2) in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = lt(v1, v2) in
      return r
  | %s(l, x, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let new_env = %s(env, x, v1) in
      let r = %s(e2, new_env, defs) in
      return r
  | %s(l, fid, e1) ->
      let v = %s(e1, env, defs) in
      let body = %s(defs, fid) in
      let empty_env = %s() in
      let x0 = 0 in
      let call_env = %s(empty_env, x0, v) in
      let r = %s(body, call_env, defs) in
      return r
  | %s(l, fid, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let body = %s(defs, fid) in
      let empty_env = %s() in
      let x0 = 0 in
      let call_env1 = %s(empty_env, x0, v1) in
      let x1 = 1 in
      let call_env2 = %s(call_env1, x1, v2) in
      let r = %s(body, call_env2, defs) in
      return r
  | %s(l, fid, e1, e2, e3) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let v3 = %s(e3, env, defs) in
      let body = %s(defs, fid) in
      let empty_env = %s() in
      let x0 = 0 in
      let call_env1 = %s(empty_env, x0, v1) in
      let x1 = 1 in
      let call_env2 = %s(call_env1, x1, v2) in
      let x2 = 2 in
      let call_env3 = %s(call_env2, x2, v3) in
      let r = %s(body, call_env3, defs) in
      return r
  | %s(l, e1, e2, e3) ->
      let v1 = %s(e1, env, defs) in
      match v1 == 0 with
      | %s() ->
          let r = %s(e2, env, defs) in
          return r
      | %s() ->
          let r = %s(e3, env, defs) in
          return r
      end
  end ;

main =
  match %s with
  | %s(defs, e) ->
      let empty_env = %s() in
      let x0 = 0 in
      let initial_env = %s(empty_env, x0, %s) in
      let r = %s(e, initial_env, defs) in
      return r
  end
|source}
    (* fundef *)
    f_fundef t_fun t_true t_false f_fundef
    (* lookup *)
    f_lookup t_extend t_true t_false f_lookup
    (* extend *)
    f_extend t_extend
    (* eval *)
    f_eval
    (* Int *)
    t_int
    (* Var *)
    t_var f_lookup
    (* Add *)
    t_add f_eval f_eval
    (* Sub *)
    t_sub f_eval f_eval
    (* Mul *)
    t_mul f_eval f_eval
    (* Div *)
    t_div f_eval f_eval
    (* Mod *)
    t_mod f_eval f_eval
    (* Lt *)
    t_lt f_eval f_eval
    (* Let *)
    t_let f_eval f_extend f_eval
    (* App *)
    t_app f_eval f_fundef t_empty f_extend f_eval
    (* App2 *)
    t_app2 f_eval f_eval f_fundef t_empty f_extend f_extend f_eval
    (* App3 *)
    t_app3 f_eval f_eval f_eval f_fundef t_empty f_extend f_extend f_extend
    f_eval
    (* Ifz *)
    t_ifz f_eval t_true f_eval t_false f_eval
    (* main *)
    arg_p t_prog t_empty f_extend arg_arg f_eval

(** {1 The assembled program} *)

(** The interpreter [I_S^T] as a complete S program, obtained by parsing
    {!source}. Its [main] label is the body of the paper's [main(p, arg)]. *)
let program : S_syntax.program = S_parser.parse source

(** {1 Driver} *)

(** Evaluate a T program by running [I_S^T] on the concrete S machine: encode the
    program, run from [main] with [p] bound to that S value and [arg] to a
    starting integer (default [0], the paper's [main(p, arg)] convention), and
    decode the resulting S value back to a T value. *)
let eval_t ?(arg : T_encoding.value = 0) (p : T_encoding.program) :
    T_encoding.value =
  let encoded_p = T_encoding.enc_program p in
  let env =
    S_cek.Env.add arg_p encoded_p
      (S_cek.Env.add arg_arg (T_encoding.enc_value arg) S_cek.Env.empty)
  in
  let result = S_cek.run_value ~env program in
  T_encoding.dec_value result
