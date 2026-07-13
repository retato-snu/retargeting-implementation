(** The auxiliary-family certificate (def:auxfam), read off the interpreter text.

    Specialization may replace a call to an auxiliary function ([lookup],
    [fundef], [extend]) by an abstract denotation only if that function really is
    the operation the denotation implements, and only if each field of the
    encoded T syntax really carries the role the specializer assumes. This module
    establishes both from {!Interp_st.program} rather than assuming them: it
    reads the interpreter through the ordinary S syntax, checks the three
    auxiliary functions against their expected shapes, checks the [eval]
    dispatch, and records the residual operation skeleton the specializer emits.
    If any shape stops matching, the certificate is {e rejected} — the
    specialization is refused rather than silently applied to an interpreter it
    no longer fits. {!Calc_pe} consumes it. *)

module S = S_syntax
module T = T_encoding

(** The recognizer's field roles. These are finer than the paper's [Role]
    (§sec:posdisamb): they split a static [Int] literal ([Static_lit]) from a
    dynamic integer ([Dyn_int]) and name the [Code]/[Defs]/[Prog] ADT wrappers,
    distinctions the PE story needs but the value domain does not. The coarser
    paper role map — the one the disambiguated value domain {!Domain_dis}
    consumes — is {!Role} ({!Role.fields} is the promotion of {!fields_of_tag};
    [tests/test_role.ml] pins the projection). *)
type role =
  | Code
  | Defs
  | Prog
  | Env
  | Dyn_int
  | Static_label
  | Static_var
  | Static_fun
  | Static_lit
  | Static_bool

type aux_primitive = Env_find | Static_fundef_lookup | Env_extend

type residual_op =
  | Emit_int_literal
  | Read_env
  | Eval_boundary
  | Extend_env
  | Lookup_fundef
  | Make_empty_env
  | Add_int
  | Sub_int
  | Mul_int
  | Div_int
  | Mod_int
  | Lt_int
  | Test_eq

type aux_summary = {
  name : string;
  args : role list;
  result : role;
  primitive : aux_primitive;
}

type eval_case = {
  tag : string;
  fields : role list;
  ops : residual_op list;
}

type certificate = {
  aux : aux_summary list;
  eval_cases : eval_case list;
  main_ops : residual_op list;
}

let string_of_role = function
  | Code -> "Code"
  | Defs -> "Defs"
  | Prog -> "Prog"
  | Env -> "Env"
  | Dyn_int -> "DynInt"
  | Static_label -> "StaticLabel"
  | Static_var -> "StaticVar"
  | Static_fun -> "StaticFun"
  | Static_lit -> "StaticLit"
  | Static_bool -> "StaticBool"

let string_of_aux_primitive = function
  | Env_find -> "env_find"
  | Static_fundef_lookup -> "static_fundef_lookup"
  | Env_extend -> "env_extend"

let string_of_residual_op = function
  | Emit_int_literal -> "emit_int_literal"
  | Read_env -> "env_find"
  | Eval_boundary -> "eval_boundary"
  | Extend_env -> "env_extend"
  | Lookup_fundef -> "static_fundef_lookup"
  | Make_empty_env -> "env_empty"
  | Add_int -> "aint_add"
  | Sub_int -> "aint_sub"
  | Mul_int -> "aint_mul"
  | Div_int -> "aint_div"
  | Mod_int -> "aint_mod"
  | Lt_int -> "aint_lt"
  | Test_eq -> "aint_eq"

let fields_of_tag (tag : string) : role list option =
  if String.equal tag T.tag_int then Some [ Static_label; Static_lit ]
  else if String.equal tag T.tag_var then Some [ Static_label; Static_var ]
  else if
    String.equal tag T.tag_add || String.equal tag T.tag_sub
    || String.equal tag T.tag_mul || String.equal tag T.tag_div
    || String.equal tag T.tag_mod || String.equal tag T.tag_lt
  then Some [ Static_label; Code; Code ]
  else if String.equal tag T.tag_let then
    Some [ Static_label; Static_var; Code; Code ]
  else if String.equal tag T.tag_app then Some [ Static_label; Static_fun; Code ]
  else if String.equal tag T.tag_app2 then
    Some [ Static_label; Static_fun; Code; Code ]
  else if String.equal tag T.tag_app3 then
    Some [ Static_label; Static_fun; Code; Code; Code ]
  else if String.equal tag T.tag_ifz then
    Some [ Static_label; Code; Code; Code ]
  else if String.equal tag T.tag_fun then Some [ Static_fun; Code; Defs ]
  else if String.equal tag T.tag_eof then Some []
  else if String.equal tag T.tag_extend then Some [ Static_var; Dyn_int; Env ]
  else if String.equal tag T.tag_empty then Some []
  else if String.equal tag T.tag_prog then Some [ Defs; Code ]
  else if String.equal tag Interp_st.t_true || String.equal tag Interp_st.t_false
  then Some []
  else None

exception Reject of string

let reject msg = raise (Reject msg)

let cmd_at (p : S.program) (l : Label.t) : S.cmd =
  try S.cmd_at p l with Invalid_argument msg -> reject msg

let find_fun (p : S.program) (name : string) : S.fundef =
  match List.find_opt (fun d -> String.equal d.S.name name) p.S.funs with
  | Some d -> d
  | None -> reject ("missing function " ^ name)

let expect_var (want : string) = function
  | S.EVar x when String.equal x want -> ()
  | _ -> reject ("expected variable " ^ want)

let expect_int (want : int) = function
  | S.EInt n when n = want -> ()
  | _ -> reject (Printf.sprintf "expected integer %d" want)

let expect_return_var p l x =
  match cmd_at p l with
  | S.Return (S.EVar y) when String.equal x y -> ()
  | _ -> reject ("expected return " ^ x)

let branch_label tag branches =
  match
    List.find_opt
      (fun (S.PTag (tag', _), _) -> String.equal tag tag')
      branches
  with
  | Some (_, l) -> l
  | None -> reject ("missing branch " ^ tag)

(* The key comparison of [lookup] / [fundef]: the sought id against the cons's
   key, S's [==] at an identifier role. *)
let expect_key_eq e x y =
  match e with
  | S.EPrim ("eq", [ S.EVar a; S.EVar b ])
    when String.equal a x && String.equal b y ->
      ()
  | _ -> reject ("expected " ^ x ^ " == " ^ y)

let expect_letcall p l ~fname ~args =
  match cmd_at p l with
  | S.LetCall (x, f, es, k)
    when String.equal f fname && List.length es = List.length args ->
      List.iter2 expect_var args es;
      (x, k)
  | _ -> reject ("expected call to " ^ fname)

let expect_let_prim p l ~prim ~args =
  match cmd_at p l with
  | S.Let (x, S.EPrim (op, es), k)
    when String.equal op prim && List.length es = List.length args ->
      List.iter2 expect_var args es;
      (x, k)
  | _ -> reject ("expected primitive " ^ prim)

let expect_let_tag p l ~tag ~args =
  match cmd_at p l with
  | S.Let (x, S.ETag (_, tag', es), k)
    when String.equal tag tag' && List.length es = List.length args ->
      List.iter2 expect_var args es;
      (x, k)
  | _ -> reject ("expected constructor " ^ tag)

let expect_let_int p l n =
  match cmd_at p l with
  | S.Let (x, e, k) ->
      expect_int n e;
      (x, k)
  | _ -> reject "expected integer let"

let expect_match_var p l v =
  match cmd_at p l with
  | S.Match (e, branches) ->
      expect_var v e;
      branches
  | _ -> reject ("expected match on " ^ v)

(* The [Ifz] test: the scrutinee's value against [0]. *)
let expect_match_eq_zero p l v =
  match cmd_at p l with
  | S.Match (S.EPrim ("eq", [ S.EVar x; S.EInt 0 ]), branches)
    when String.equal x v ->
      branches
  | _ -> reject ("expected match on " ^ v ^ " == 0")

let recognize_extend p =
  let d = find_fun p Interp_st.f_extend in
  match d.S.params with
  | [ env; x; v ] ->
      let r, k =
        expect_let_tag p d.S.entry ~tag:T.tag_extend ~args:[ x; v; env ]
      in
      expect_return_var p k r;
      {
        name = d.S.name;
        args = [ Env; Static_var; Dyn_int ];
        result = Env;
        primitive = Env_extend;
      }
  | _ -> reject "extend has unexpected parameters"

let recognize_lookup p =
  let d = find_fun p Interp_st.f_lookup in
  match d.S.params with
  | [ env; xid ] -> (
      match expect_match_var p d.S.entry env with
      | [ (S.PTag (tag, [ xid2; v; rest ]), l) ]
        when String.equal tag T.tag_extend -> (
          match cmd_at p l with
          | S.Match (test, branches) ->
              expect_key_eq test xid xid2;
              let t = branch_label Interp_st.t_true branches in
              let f = branch_label Interp_st.t_false branches in
              expect_return_var p t v;
              let r, k =
                expect_letcall p f ~fname:Interp_st.f_lookup ~args:[ rest; xid ]
              in
              expect_return_var p k r;
              {
                name = d.S.name;
                args = [ Env; Static_var ];
                result = Dyn_int;
                primitive = Env_find;
              }
          | _ -> reject "lookup should compare the requested key")
      | _ -> reject "lookup should match an Extend spine")
  | _ -> reject "lookup has unexpected parameters"

let recognize_fundef p =
  let d = find_fun p Interp_st.f_fundef in
  match d.S.params with
  | [ defs; fid ] -> (
      match expect_match_var p d.S.entry defs with
      | [ (S.PTag (tag, [ fid2; body; rest ]), l) ]
        when String.equal tag T.tag_fun -> (
          match cmd_at p l with
          | S.Match (test, branches) ->
              expect_key_eq test fid fid2;
              let t = branch_label Interp_st.t_true branches in
              let f = branch_label Interp_st.t_false branches in
              expect_return_var p t body;
              let r, k =
                expect_letcall p f ~fname:Interp_st.f_fundef ~args:[ rest; fid ]
              in
              expect_return_var p k r;
              {
                name = d.S.name;
                args = [ Defs; Static_fun ];
                result = Code;
                primitive = Static_fundef_lookup;
              }
          | _ -> reject "fundef should compare the requested key")
      | _ -> reject "fundef should match a Fun spine")
  | _ -> reject "fundef has unexpected parameters"

let recognize_int_branch p l vars =
  match vars with
  | [ _lab; n ] ->
      let r, k =
        match cmd_at p l with
        | S.Let (r, e, k) ->
            expect_var n e;
            (r, k)
        | _ -> reject "Int branch should bind the literal"
      in
      expect_return_var p k r;
      [ Emit_int_literal ]
  | _ -> reject "Int branch fields changed"

let recognize_var_branch p l env vars =
  match vars with
  | [ _lab; xid ] ->
      let r, k = expect_letcall p l ~fname:Interp_st.f_lookup ~args:[ env; xid ] in
      expect_return_var p k r;
      [ Read_env ]
  | _ -> reject "Var branch fields changed"

let recognize_binary_branch p l env defs prim vars =
  match vars with
  | [ _lab; e1; e2 ] ->
      let v1, k1 =
        expect_letcall p l ~fname:Interp_st.f_eval ~args:[ e1; env; defs ]
      in
      let v2, k2 =
        expect_letcall p k1 ~fname:Interp_st.f_eval ~args:[ e2; env; defs ]
      in
      let r, k3 = expect_let_prim p k2 ~prim ~args:[ v1; v2 ] in
      expect_return_var p k3 r;
      let op =
        match prim with
        | "add" -> Add_int
        | "sub" -> Sub_int
        | "mul" -> Mul_int
        | "div" -> Div_int
        | "mod" -> Mod_int
        | "lt" -> Lt_int
        | _ -> reject ("unexpected binary primitive " ^ prim)
      in
      [ Eval_boundary; Eval_boundary; op ]
  | _ -> reject "binary branch fields changed"

let recognize_let_branch p l env defs vars =
  match vars with
  | [ _lab; x; e1; e2 ] ->
      let v1, k1 =
        expect_letcall p l ~fname:Interp_st.f_eval ~args:[ e1; env; defs ]
      in
      let new_env, k2 =
        expect_letcall p k1 ~fname:Interp_st.f_extend ~args:[ env; x; v1 ]
      in
      let r, k3 =
        expect_letcall p k2 ~fname:Interp_st.f_eval ~args:[ e2; new_env; defs ]
      in
      expect_return_var p k3 r;
      [ Eval_boundary; Extend_env; Eval_boundary ]
  | _ -> reject "Let branch fields changed"

let recognize_app_branch p l env defs vars =
  match vars with
  | [ _lab; fid; e1 ] ->
      let v, k1 =
        expect_letcall p l ~fname:Interp_st.f_eval ~args:[ e1; env; defs ]
      in
      let body, k2 =
        expect_letcall p k1 ~fname:Interp_st.f_fundef ~args:[ defs; fid ]
      in
      let empty_env, k3 = expect_let_tag p k2 ~tag:T.tag_empty ~args:[] in
      let x0, k4 = expect_let_int p k3 0 in
      let call_env, k5 =
        expect_letcall p k4 ~fname:Interp_st.f_extend
          ~args:[ empty_env; x0; v ]
      in
      let r, k6 =
        expect_letcall p k5 ~fname:Interp_st.f_eval
          ~args:[ body; call_env; defs ]
      in
      expect_return_var p k6 r;
      [ Eval_boundary; Lookup_fundef; Make_empty_env; Extend_env; Eval_boundary ]
  | _ -> reject "App branch fields changed"

(* App2(l, fid, e1, e2) => two operand evals, a fundef lookup, then two [extend]s
   consing the [[0↦v1; 1↦v2]] environment before the body eval. Structurally the
   App branch with a second operand eval and a second extend. *)
let recognize_app2_branch p l env defs vars =
  match vars with
  | [ _lab; fid; e1; e2 ] ->
      let v1, k1 =
        expect_letcall p l ~fname:Interp_st.f_eval ~args:[ e1; env; defs ]
      in
      let v2, k2 =
        expect_letcall p k1 ~fname:Interp_st.f_eval ~args:[ e2; env; defs ]
      in
      let body, k3 =
        expect_letcall p k2 ~fname:Interp_st.f_fundef ~args:[ defs; fid ]
      in
      let empty_env, k4 = expect_let_tag p k3 ~tag:T.tag_empty ~args:[] in
      let x0, k5 = expect_let_int p k4 0 in
      let call_env1, k6 =
        expect_letcall p k5 ~fname:Interp_st.f_extend ~args:[ empty_env; x0; v1 ]
      in
      let x1, k7 = expect_let_int p k6 1 in
      let call_env2, k8 =
        expect_letcall p k7 ~fname:Interp_st.f_extend ~args:[ call_env1; x1; v2 ]
      in
      let r, k9 =
        expect_letcall p k8 ~fname:Interp_st.f_eval ~args:[ body; call_env2; defs ]
      in
      expect_return_var p k9 r;
      [ Eval_boundary; Eval_boundary; Lookup_fundef; Make_empty_env; Extend_env;
        Extend_env; Eval_boundary ]
  | _ -> reject "App2 branch fields changed"

(* App3(l, fid, e1, e2, e3) => three operand evals then three [extend]s. *)
let recognize_app3_branch p l env defs vars =
  match vars with
  | [ _lab; fid; e1; e2; e3 ] ->
      let v1, k1 =
        expect_letcall p l ~fname:Interp_st.f_eval ~args:[ e1; env; defs ]
      in
      let v2, k2 =
        expect_letcall p k1 ~fname:Interp_st.f_eval ~args:[ e2; env; defs ]
      in
      let v3, k3 =
        expect_letcall p k2 ~fname:Interp_st.f_eval ~args:[ e3; env; defs ]
      in
      let body, k4 =
        expect_letcall p k3 ~fname:Interp_st.f_fundef ~args:[ defs; fid ]
      in
      let empty_env, k5 = expect_let_tag p k4 ~tag:T.tag_empty ~args:[] in
      let x0, k6 = expect_let_int p k5 0 in
      let call_env1, k7 =
        expect_letcall p k6 ~fname:Interp_st.f_extend ~args:[ empty_env; x0; v1 ]
      in
      let x1, k8 = expect_let_int p k7 1 in
      let call_env2, k9 =
        expect_letcall p k8 ~fname:Interp_st.f_extend ~args:[ call_env1; x1; v2 ]
      in
      let x2, k10 = expect_let_int p k9 2 in
      let call_env3, k11 =
        expect_letcall p k10 ~fname:Interp_st.f_extend ~args:[ call_env2; x2; v3 ]
      in
      let r, k12 =
        expect_letcall p k11 ~fname:Interp_st.f_eval ~args:[ body; call_env3; defs ]
      in
      expect_return_var p k12 r;
      [ Eval_boundary; Eval_boundary; Eval_boundary; Lookup_fundef;
        Make_empty_env; Extend_env; Extend_env; Extend_env; Eval_boundary ]
  | _ -> reject "App3 branch fields changed"

let recognize_ifz_branch p l env defs vars =
  match vars with
  | [ _lab; e1; e2; e3 ] ->
      let v1, k1 =
        expect_letcall p l ~fname:Interp_st.f_eval ~args:[ e1; env; defs ]
      in
      let branches = expect_match_eq_zero p k1 v1 in
      let t = branch_label Interp_st.t_true branches in
      let f = branch_label Interp_st.t_false branches in
      let rt, kt =
        expect_letcall p t ~fname:Interp_st.f_eval ~args:[ e2; env; defs ]
      in
      expect_return_var p kt rt;
      let rf, kf =
        expect_letcall p f ~fname:Interp_st.f_eval ~args:[ e3; env; defs ]
      in
      expect_return_var p kf rf;
      [ Eval_boundary; Test_eq; Eval_boundary; Eval_boundary ]
  | _ -> reject "Ifz branch fields changed"

let recognize_eval p =
  let d = find_fun p Interp_st.f_eval in
  match d.S.params with
  | [ e; env; defs ] ->
      let branches = expect_match_var p d.S.entry e in
      List.map
        (fun (S.PTag (tag, vars), l) ->
          let fields =
            match fields_of_tag tag with
            | Some fs -> fs
            | None -> reject ("unknown T-code tag " ^ tag)
          in
          if List.length fields <> List.length vars then
            reject ("arity mismatch for tag " ^ tag);
          let ops =
            if String.equal tag T.tag_int then recognize_int_branch p l vars
            else if String.equal tag T.tag_var then
              recognize_var_branch p l env vars
            else if String.equal tag T.tag_add then
              recognize_binary_branch p l env defs "add" vars
            else if String.equal tag T.tag_sub then
              recognize_binary_branch p l env defs "sub" vars
            else if String.equal tag T.tag_mul then
              recognize_binary_branch p l env defs "mul" vars
            else if String.equal tag T.tag_div then
              recognize_binary_branch p l env defs "div" vars
            else if String.equal tag T.tag_mod then
              recognize_binary_branch p l env defs "mod" vars
            else if String.equal tag T.tag_lt then
              recognize_binary_branch p l env defs "lt" vars
            else if String.equal tag T.tag_let then
              recognize_let_branch p l env defs vars
            else if String.equal tag T.tag_app then
              recognize_app_branch p l env defs vars
            else if String.equal tag T.tag_app2 then
              recognize_app2_branch p l env defs vars
            else if String.equal tag T.tag_app3 then
              recognize_app3_branch p l env defs vars
            else if String.equal tag T.tag_ifz then
              recognize_ifz_branch p l env defs vars
            else reject ("unexpected eval tag " ^ tag)
          in
          { tag; fields; ops })
        branches
  | _ -> reject "eval has unexpected parameters"

let recognize_main p =
  let branches = expect_match_var p p.S.main Interp_st.arg_p in
  match branches with
  | [ (S.PTag (tag, [ defs; e ]), l) ] when String.equal tag T.tag_prog ->
      let empty_env, k1 = expect_let_tag p l ~tag:T.tag_empty ~args:[] in
      let x0, k2 = expect_let_int p k1 0 in
      let initial_env, k3 =
        expect_letcall p k2 ~fname:Interp_st.f_extend
          ~args:[ empty_env; x0; Interp_st.arg_arg ]
      in
      let r, k4 =
        expect_letcall p k3 ~fname:Interp_st.f_eval
          ~args:[ e; initial_env; defs ]
      in
      expect_return_var p k4 r;
      [ Make_empty_env; Extend_env; Eval_boundary ]
  | _ -> reject "main should destructure Prog(defs, e)"

let certify (p : S.program) : (certificate, string list) result =
  let errors = ref [] in
  let run name f =
    try Some (f p)
    with Reject msg ->
      errors := (name ^ ": " ^ msg) :: !errors;
      None
  in
  let lookup = run "lookup" recognize_lookup in
  let fundef = run "fundef" recognize_fundef in
  let extend = run "extend" recognize_extend in
  let eval_cases = run "eval" recognize_eval in
  let main_ops = run "main" recognize_main in
  match !errors with
  | _ :: _ -> Error (List.rev !errors)
  | [] ->
      Ok
        {
          aux =
            [
              Option.get lookup;
              Option.get fundef;
              Option.get extend;
            ];
          eval_cases = Option.get eval_cases;
          main_ops = Option.get main_ops;
        }

let certify_interp_st () = certify Interp_st.program
