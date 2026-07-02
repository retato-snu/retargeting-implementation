(** [I_S^T]: a definitional interpreter for the target language T, written as an S program ({!S_syntax.program}); transcribes the paper's S-coded interpreter (main.tex l.356-435). *)

let t_int = "Int"
let t_var = "Var"
let t_sub = "Sub"
let t_mul = "Mul"
let t_let = "Let"
let t_app = "App"
let t_ifz = "Ifz"
let t_fun = "Fun"
let t_nil = "Nil"
let t_env = "Env"
let t_defs = "Defs"
let t_prog = "Prog"

let t_true = "True"
let t_false = "False"

let f_eval = "eval"
let f_lookup = "lookup"
let f_fundef = "fundef"
let f_extend = "extend"

let arg_p = "p"
let arg_arg = "arg"

(** The five S functions ([eval], [lookup], [fundef], [extend]) and [main] in relaxed-ANF surface syntax, matching the paper's listing (main.tex l.356-435). *)
let source : string =
  Printf.sprintf
    {source|
def %s(defs, fid) =
  match defs with
  | %s(f, body, rest) ->
      match f with
      | %s(fid2) ->
          match iszero(fid - fid2) with
          | %s() -> return body
          | %s() ->
              let r = %s(rest, fid) in
              return r
          end
      end
  end ;

def %s(env, xid) =
  match env with
  | %s(x, val, rest) ->
      match x with
      | %s(l, xid2) ->
          match iszero(xid - xid2) with
          | %s() -> return val
          | %s() ->
              let r = %s(rest, xid) in
              return r
          end
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
      let r = v1 - v2 in
      return r
  | %s(l, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let v2 = %s(e2, env, defs) in
      let r = v1 * v2 in
      return r
  | %s(l, x, e1, e2) ->
      let v1 = %s(e1, env, defs) in
      let new_env = %s(env, x, v1) in
      let r = %s(e2, new_env, defs) in
      return r
  | %s(l, f, e1) ->
      match f with
      | %s(fid) ->
          let v = %s(e1, env, defs) in
          let body = %s(defs, fid) in
          let empty_env = %s() in
          let l0 = 0 in
          let x0 = 0 in
          let x = %s(l0, x0) in
          let call_env = %s(empty_env, x, v) in
          let r = %s(body, call_env, defs) in
          return r
      end
  | %s(l, e1, e2, e3) ->
      let v1 = %s(e1, env, defs) in
      match iszero(v1) with
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
      let l0 = 0 in
      let x0 = 0 in
      let x = %s(l0, x0) in
      let initial_env = %s(empty_env, x, %s) in
      let r = %s(e, initial_env, defs) in
      return r
  end
|source}
    f_fundef t_defs t_fun t_true t_false f_fundef
    f_lookup t_env t_var t_true t_false f_lookup
    f_extend t_env
    f_eval
    t_int
    t_var f_lookup
    t_sub f_eval f_eval
    t_mul f_eval f_eval
    t_let f_eval f_extend f_eval
    t_app t_fun f_eval f_fundef t_nil t_var f_extend f_eval
    t_ifz f_eval t_true f_eval t_false f_eval
    arg_p t_prog t_nil t_var f_extend arg_arg f_eval

(** The interpreter [I_S^T] as a complete S program, obtained by parsing {!source}. *)
let program : S_syntax.program = S_parser.parse source

(** Evaluate a T program by running [I_S^T] on the concrete S machine. *)
let eval_t ?(arg : T_encoding.value = 0) (p : T_encoding.program) :
    T_encoding.value =
  let encoded_p = T_encoding.enc_program p in
  let env =
    S_cek.Env.add arg_p encoded_p
      (S_cek.Env.add arg_arg (T_encoding.enc_value arg) S_cek.Env.empty)
  in
  let result = S_cek.run_value ~env program in
  T_encoding.dec_value result
