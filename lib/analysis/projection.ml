(** Concrete S -> T projection and its verification.

    This module realizes the paper's projection [⌊·⌋] on {e machine states},
    together with the macro-step bisimulation check: running the S-coded
    interpreter {!Interp_st} ([I_S^T]) on the concrete S machine {!S_cek},
    observing the resulting S trace only at the recursive [eval] entry and return
    points, and decoding each observed state, yields a run of the T machine
    {!T_machine}.

    - {!Points} extracts, structurally from {!Interp_st.program}, the observation
      labels (the eval-entry [match] and the eval-return labels [L_ret]), the
      eval-call labels [L_call], and the T continuation frame each call label
      stands for — the paper's context-binding map [β_ℓ]. No label is hardcoded
      as a number; all are recovered by matching the command structure.
    - {!Decode} is [⌊·⌋] on states: at an eval-entry the control is the decoded T
      expression bound to [eval]'s [e] parameter, at an eval-return the raw
      integer in the return variable; the environment is the decoded [env]
      parameter; the continuation decodes, via [β_ℓ], each S frame whose
      suspended call is an eval-call site, skipping frames suspended at auxiliary
      or root call sites.
    - {!verify} checks that consecutive decoded states are connected by exactly
      one {!T_machine.step}; {!equals_t_machine} additionally cross-checks the
      decoded sequence against the T machine's own run of the same program. *)

(** {1 Interpreter points} *)

module Points = struct
  (** The T continuation frame a recursive [eval] call site stands for — the
      paper's [β_ℓ]. Each constructor names the S variables, read in the frame's
      {e saved} environment, that supply the decoded T frame's payload: the
      pending operand expression when the left operand is under evaluation
      ([FSub1] …), the already-evaluated left operand when the right one is
      ([FSub2] …), the bound variable and body for a [let], the environment to
      reinstate when a [let]/function body is under evaluation ([FRestore]), the
      two branch expressions for an [ifz] scrutinee, and nothing for an [ifz]
      branch itself ([FSilent]). In the application frames the variables are, in
      order, the callee id, then the already-evaluated operand values, then the
      pending operand expressions. {!Decode.frame} performs the decode. *)
  type frame_kind =
    | FAdd1 of S_syntax.var
    | FAdd2 of S_syntax.var
    | FSub1 of S_syntax.var
    | FSub2 of S_syntax.var
    | FMul1 of S_syntax.var
    | FMul2 of S_syntax.var
    | FDiv1 of S_syntax.var
    | FDiv2 of S_syntax.var
    | FMod1 of S_syntax.var
    | FMod2 of S_syntax.var
    | FLt1 of S_syntax.var
    | FLt2 of S_syntax.var
    | FLet of S_syntax.var * S_syntax.var
    | FApp of S_syntax.var
    | FApp2_1 of S_syntax.var * S_syntax.var
    | FApp2_2 of S_syntax.var * S_syntax.var
    | FApp3_1 of S_syntax.var * S_syntax.var * S_syntax.var
    | FApp3_2 of S_syntax.var * S_syntax.var * S_syntax.var
    | FApp3_3 of S_syntax.var * S_syntax.var * S_syntax.var
    | FRestore of S_syntax.var
    | FIfz of S_syntax.var * S_syntax.var
    | FSilent

  type t = {
    eval_entry : Label.t;  (** the eval-entry [match] label (the paper's [match]) *)
    eval_e : S_syntax.var;  (** [eval]'s expression parameter *)
    eval_env : S_syntax.var;  (** [eval]'s environment parameter *)
    ret_labels : (Label.t * S_syntax.var) list;
        (** eval-return labels, each with the variable holding the returned
            integer (the paper's [L_ret] with the [ρ[r]] read) *)
    call_frames : (Label.t * frame_kind) list;
        (** eval-call labels (the paper's [L_call]), each with the T frame role
            its suspended frame decodes to (the paper's [β_ℓ]) *)
  }

  exception Extraction_error of string

  let fail fmt = Printf.ksprintf (fun s -> raise (Extraction_error s)) fmt

  let cmd_at (l : Label.t) : S_syntax.cmd = S_syntax.cmd_at Interp_st.program l

  let find_fun (name : string) : S_syntax.fundef =
    match
      List.find_opt
        (fun (d : S_syntax.fundef) -> String.equal d.S_syntax.name name)
        Interp_st.program.S_syntax.funs
    with
    | Some d -> d
    | None -> fail "interpreter does not define %s" name

  let is_var (x : S_syntax.var) (a : S_syntax.exp) : bool =
    match a with S_syntax.EVar y -> String.equal x y | _ -> false

  (* A recursive [eval] call site evaluating subexpression [sub] under the
     interpreter's [env]/[defs] parameters, i.e. [let _ = eval(sub, env, defs)
     in k] — the eval-call shape the paper fixes. Returns the call's label and
     the continuation label [k]. *)
  let as_eval_call (env : S_syntax.var) (defs : S_syntax.var)
      (sub : S_syntax.var) (l : Label.t) : (Label.t * Label.t) option =
    match cmd_at l with
    | S_syntax.LetCall (_, f, [ a0; a1; a2 ], k)
      when String.equal f Interp_st.f_eval
           && is_var sub a0 && is_var env a1 && is_var defs a2 ->
        Some (l, k)
    | _ -> None

  let expect_eval_call ctx env defs sub l =
    match as_eval_call env defs sub l with
    | Some r -> r
    | None -> fail "%s: expected eval(%s, %s, %s)" ctx sub env defs

  let expect_return ctx l =
    match cmd_at l with
    | S_syntax.Return (S_syntax.EVar r) -> (l, r)
    | _ -> fail "%s: expected a return command" ctx

  let branch tag branches =
    match
      List.find_opt
        (fun (S_syntax.PTag (t, _), _) -> String.equal t tag)
        branches
    with
    | Some (S_syntax.PTag (_, vars), l) -> (vars, l)
    | None -> fail "missing %s branch" tag

  (* The eval entry must be a [match] on the [e] parameter; return its branches. *)
  let eval_branches (eval : S_syntax.fundef) (e : S_syntax.var) =
    match cmd_at eval.S_syntax.entry with
    | S_syntax.Match (a, branches) when is_var e a -> branches
    | _ -> fail "eval body must match its expression parameter"

  (* Extract every interpreter point structurally from the interpreter program. *)
  let extract () : t =
    let eval = find_fun Interp_st.f_eval in
    let e, env, defs =
      match eval.S_syntax.params with
      | [ e; env; defs ] -> (e, env, defs)
      | _ -> fail "eval must take exactly three parameters"
    in
    let branches = eval_branches eval e in

    let rets = ref [] in
    let calls = ref [] in
    let add_ret r = rets := r :: !rets in
    let add_call c = calls := c :: !calls in

    (* Int(l, n) => let r = n in return r. *)
    let () =
      let vars, body = branch T_encoding.tag_int branches in
      (match vars with
      | [ _l; _n ] -> ()
      | _ -> fail "Int branch must bind label and value");
      match cmd_at body with
      | S_syntax.Let (r, _rhs, k) -> add_ret (expect_return "Int return" k);
          ignore r
      | _ -> fail "Int branch must bind the result then return it"
    in

    (* Var(l, xid) => let r = lookup(env, xid) in return r. The lookup call is an
       auxiliary call, not an eval-call, so it pushes no observed frame. *)
    let () =
      let _vars, body = branch T_encoding.tag_var branches in
      match cmd_at body with
      | S_syntax.LetCall (_, f, _, k) when String.equal f Interp_st.f_lookup ->
          add_ret (expect_return "Var return" k)
      | _ -> fail "Var branch must call lookup then return"
    in

    (* Binary(l, e1, e2) => let v1 = eval(e1) in let v2 = eval(e2) in
                            let r = op(v1, v2) in return r. *)
    let binary tag op fk1 fk2 =
      let vars, body = branch tag branches in
      let _l, e1, e2 =
        match vars with
        | [ l; e1; e2 ] -> (l, e1, e2)
        | _ -> fail "%s branch must bind label and two subexpressions" tag
      in
      let call1, after1 = expect_eval_call (tag ^ " left") env defs e1 body in
      add_call (call1, fk1 e2);
      let call2, after2 = expect_eval_call (tag ^ " right") env defs e2 after1 in
      let v1 =
        match cmd_at call1 with
        | S_syntax.LetCall (v1, _, _, _) -> v1
        | _ -> fail "%s left call malformed" tag
      in
      add_call (call2, fk2 v1);
      match cmd_at after2 with
      | S_syntax.Let (r, S_syntax.EPrim (o, _), k) when String.equal o op ->
          add_ret (expect_return (tag ^ " return") k);
          ignore r
      | _ -> fail "%s branch must apply %s then return" tag op
    in
    binary T_encoding.tag_add "add" (fun e2 -> FAdd1 e2) (fun v1 -> FAdd2 v1);
    binary T_encoding.tag_sub "sub" (fun e2 -> FSub1 e2) (fun v1 -> FSub2 v1);
    binary T_encoding.tag_mul "mul" (fun e2 -> FMul1 e2) (fun v1 -> FMul2 v1);
    (* Div/Mod/Lt branches are structurally identical to Sub/Mul, so the generic
       [binary] extractor handles them with their own frame roles. *)
    binary T_encoding.tag_div "div" (fun e2 -> FDiv1 e2) (fun v1 -> FDiv2 v1);
    binary T_encoding.tag_mod "mod" (fun e2 -> FMod1 e2) (fun v1 -> FMod2 v1);
    binary T_encoding.tag_lt "lt" (fun e2 -> FLt1 e2) (fun v1 -> FLt2 v1);

    (* Let(l, x, e1, e2) => let v1 = eval(e1) in let new_env = extend(env, x, v1)
                            in let r = eval(e2, new_env, defs) in return r.
       The bound-expression call carries a Let frame, the body call a Restore
       frame; extend is auxiliary and pushes no observed frame. *)
    let () =
      let vars, body = branch T_encoding.tag_let branches in
      let x, e1, e2 =
        match vars with
        | [ _l; x; e1; e2 ] -> (x, e1, e2)
        | _ -> fail "Let branch must bind label, var, bound, body"
      in
      let call1, after1 = expect_eval_call "Let bound" env defs e1 body in
      add_call (call1, FLet (x, e2));
      let after_extend =
        match cmd_at after1 with
        | S_syntax.LetCall (new_env, f, _, k)
          when String.equal f Interp_st.f_extend ->
            (new_env, k)
        | _ -> fail "Let branch must call extend after the bound expression"
      in
      let new_env, k = after_extend in
      let call2, after2 =
        match cmd_at k with
        | S_syntax.LetCall (_, f, [ a0; a1; a2 ], next)
          when String.equal f Interp_st.f_eval
               && is_var e2 a0 && is_var new_env a1 && is_var defs a2 ->
            (k, next)
        | _ -> fail "Let branch must evaluate the body under the extended env"
      in
      add_call (call2, FRestore env);
      ignore (expect_return "Let return" after2 |> add_ret)
    in

    (* App(l, fid, e1) =>
         let v = eval(e1) in let body = fundef(defs, fid) in ...
         let call_env = extend(...) in let r = eval(body, call_env, defs) in
         return r.
       The callee id is a plain integer bound by the branch (the plain-int ADTs
       of the disambiguated value domain — no [Fun] wrapper to unwrap). The
       argument call carries an App frame, the body call a Restore frame;
       fundef/extend are auxiliary. *)
    let () =
      let vars, app_body = branch T_encoding.tag_app branches in
      let fvar, e1 =
        match vars with
        | [ _l; f; e1 ] -> (f, e1)
        | _ -> fail "App branch must bind label, function, argument"
      in
      let call1, after1 = expect_eval_call "App argument" env defs e1 app_body in
      add_call (call1, FApp fvar);
      (* Skip the auxiliary fundef call and the constructor / cons that build the
         callee environment, until the body eval call. *)
      let rec find_body_call l =
        match cmd_at l with
        | S_syntax.LetCall (_, f, [ a0; a1; a2 ], next)
          when String.equal f Interp_st.f_eval && is_var defs a2 ->
            (* eval(body, call_env, defs): body and call_env are local names. *)
            ignore (a0, a1);
            (l, next)
        | S_syntax.Let (_, _, k)
        | S_syntax.LetCall (_, _, _, k) ->
            find_body_call k
        | _ -> fail "App branch must evaluate the function body"
      in
      let call2, after2 = find_body_call after1 in
      add_call (call2, FRestore env);
      ignore (expect_return "App return" after2 |> add_ret)
    in

    (* Walk forward from [l] over the auxiliary calls and lets that build the
       callee environment, to the body eval call [eval(body, call_env, defs)]
       (identified by its third argument being [defs]); returns its label and
       continuation. Shared by the App/App2/App3 handlers, whose
       environment-building prefixes differ only in the number of [extend]s. *)
    let find_body_call l =
      let rec go l =
        match cmd_at l with
        | S_syntax.LetCall (_, f, [ _; _; a2 ], next)
          when String.equal f Interp_st.f_eval && is_var defs a2 ->
            (l, next)
        | S_syntax.Let (_, _, k) | S_syntax.LetCall (_, _, _, k) -> go k
        | _ -> fail "multi-arg App branch must evaluate the function body"
      in
      go l
    in

    (* The result variable a [LetCall] binds (the [v1]/[v2] a later frame reads). *)
    let call_result ctx l =
      match cmd_at l with
      | S_syntax.LetCall (v, _, _, _) -> v
      | _ -> fail "%s call malformed" ctx
    in

    (* App2(l, fid, e1, e2) => two operand evals carrying [FApp2_1]/[FApp2_2],
       then the body eval carrying [FRestore]. *)
    let () =
      let vars, app_body = branch T_encoding.tag_app2 branches in
      let fvar, e1, e2 =
        match vars with
        | [ _l; f; e1; e2 ] -> (f, e1, e2)
        | _ -> fail "App2 branch must bind label, function, two arguments"
      in
      let call1, after1 = expect_eval_call "App2 operand 1" env defs e1 app_body in
      add_call (call1, FApp2_1 (fvar, e2));
      let call2, after2 = expect_eval_call "App2 operand 2" env defs e2 after1 in
      let v1 = call_result "App2 operand 1" call1 in
      add_call (call2, FApp2_2 (fvar, v1));
      let call3, after3 = find_body_call after2 in
      add_call (call3, FRestore env);
      ignore (expect_return "App2 return" after3 |> add_ret)
    in

    (* App3(l, fid, e1, e2, e3) => three operand evals carrying
       [FApp3_1]/[FApp3_2]/[FApp3_3], then the body eval carrying [FRestore]. *)
    let () =
      let vars, app_body = branch T_encoding.tag_app3 branches in
      let fvar, e1, e2, e3 =
        match vars with
        | [ _l; f; e1; e2; e3 ] -> (f, e1, e2, e3)
        | _ -> fail "App3 branch must bind label, function, three arguments"
      in
      let call1, after1 = expect_eval_call "App3 operand 1" env defs e1 app_body in
      add_call (call1, FApp3_1 (fvar, e2, e3));
      let call2, after2 = expect_eval_call "App3 operand 2" env defs e2 after1 in
      let v1 = call_result "App3 operand 1" call1 in
      add_call (call2, FApp3_2 (fvar, v1, e3));
      let call3, after3 = expect_eval_call "App3 operand 3" env defs e3 after2 in
      let v2 = call_result "App3 operand 2" call2 in
      add_call (call3, FApp3_3 (fvar, v1, v2));
      let call4, after4 = find_body_call after3 in
      add_call (call4, FRestore env);
      ignore (expect_return "App3 return" after4 |> add_ret)
    in

    (* Ifz(l, e1, e2, e3) => let v1 = eval(e1) in match v1 == 0 with
         True()  => let r = eval(e2) in return r
         False() => let r = eval(e3) in return r.
       The scrutinee call carries an Ifz frame (branches e2, e3). Each branch
       call carries a Silent frame. *)
    let () =
      let vars, body = branch T_encoding.tag_ifz branches in
      let e1, e2, e3 =
        match vars with
        | [ _l; e1; e2; e3 ] -> (e1, e2, e3)
        | _ -> fail "Ifz branch must bind label and three subexpressions"
      in
      let call1, after1 = expect_eval_call "Ifz scrutinee" env defs e1 body in
      add_call (call1, FIfz (e2, e3));
      (* The [==] prim nests directly into the scrutinee of the [match], so the
         command after the scrutinee call is the [Match] itself. *)
      let bool_branches =
        match cmd_at after1 with
        | S_syntax.Match (S_syntax.EPrim ("eq", _), bbranches) -> bbranches
        | _ -> fail "Ifz branch must match v1 == 0 directly"
      in
      let branch_call ctx sub bbranch_tag =
        let _vars, bbody = branch bbranch_tag bool_branches in
        let call, after = expect_eval_call ctx env defs sub bbody in
        add_call (call, FSilent);
        ignore (expect_return (ctx ^ " return") after |> add_ret)
      in
      branch_call "Ifz then" e2 Interp_st.t_true;
      branch_call "Ifz else" e3 Interp_st.t_false
    in

    {
      eval_entry = eval.S_syntax.entry;
      eval_e = e;
      eval_env = env;
      ret_labels = List.rev !rets;
      call_frames = List.rev !calls;
    }

  (* The variable holding the returned value at a return label, if [l] is one. *)
  let ret_var (p : t) (l : Label.t) : S_syntax.var option =
    List.find_map
      (fun (rl, v) -> if Label.equal rl l then Some v else None)
      p.ret_labels

  (* The frame role ([β_ℓ]) of an eval-call label, if [l] is one. *)
  let frame_kind (p : t) (l : Label.t) : frame_kind option =
    List.find_map
      (fun (cl, fk) -> if Label.equal cl l then Some fk else None)
      p.call_frames

  (* Is [l] an observation label (eval entry or an eval return)? *)
  let is_observed (p : t) (l : Label.t) : bool =
    Label.equal l p.eval_entry || ret_var p l <> None
end

(** {1 State decoding: the paper's [⌊·⌋] from observed S states to T states} *)

module Decode = struct
  exception Project_error of string

  let fail fmt = Printf.ksprintf (fun s -> raise (Project_error s)) fmt

  let read (ctx : string) (rho : S_cek.env) (x : S_syntax.var) : S_cek.value =
    match S_cek.Env.find_opt x rho with
    | Some v -> v
    | None -> fail "%s: variable %s not bound" ctx x

  (* Decoders from T_encoding, reused as the paper's [⌊·⌋]. *)
  let dec_expr ctx rho x = T_encoding.dec_expr (read ctx rho x)
  let dec_env ctx rho x = T_encoding.dec_env (read ctx rho x)
  let dec_var ctx rho x = T_encoding.dec_var_id ctx (read ctx rho x)
  let dec_fun ctx rho x = T_encoding.dec_fun_id ctx (read ctx rho x)

  let dec_int ctx rho x =
    match read ctx rho x with
    | S_cek.VInt n -> n
    | S_cek.VTag (t, _) -> fail "%s: expected an integer, got tag %s" ctx t

  (* Decode one S continuation frame to a T frame, if its suspended call is an
     eval-call (an element of L_call). Auxiliary and root frames decode to
     [None]: the paper's [⌊κ⌋] is oblivious to them. *)
  let frame (p : Points.t) (fr : S_cek.frame) : T_machine.frame option =
    match Points.frame_kind p fr.S_cek.suspended with
    | None -> None
    | Some fk ->
        let rho = fr.S_cek.saved_env in
        let f =
          match fk with
          | Points.FAdd1 e2 -> T_machine.Add1 (dec_expr "Add1 frame" rho e2)
          | Points.FAdd2 v1 -> T_machine.Add2 (dec_int "Add2 frame" rho v1)
          | Points.FSub1 e2 -> T_machine.Sub1 (dec_expr "Sub1 frame" rho e2)
          | Points.FSub2 v1 -> T_machine.Sub2 (dec_int "Sub2 frame" rho v1)
          | Points.FMul1 e2 -> T_machine.Mul1 (dec_expr "Mul1 frame" rho e2)
          | Points.FMul2 v1 -> T_machine.Mul2 (dec_int "Mul2 frame" rho v1)
          | Points.FDiv1 e2 -> T_machine.Div1 (dec_expr "Div1 frame" rho e2)
          | Points.FDiv2 v1 -> T_machine.Div2 (dec_int "Div2 frame" rho v1)
          | Points.FMod1 e2 -> T_machine.Mod1 (dec_expr "Mod1 frame" rho e2)
          | Points.FMod2 v1 -> T_machine.Mod2 (dec_int "Mod2 frame" rho v1)
          | Points.FLt1 e2 -> T_machine.Lt1 (dec_expr "Lt1 frame" rho e2)
          | Points.FLt2 v1 -> T_machine.Lt2 (dec_int "Lt2 frame" rho v1)
          | Points.FLet (x, e2) ->
              T_machine.Let (dec_var "Let frame var" rho x,
                             dec_expr "Let frame body" rho e2)
          | Points.FApp f -> T_machine.App (dec_fun "App frame" rho f)
          | Points.FApp2_1 (f, e2) ->
              T_machine.App2_1
                (dec_fun "App2_1 frame fun" rho f,
                 dec_expr "App2_1 frame e2" rho e2)
          | Points.FApp2_2 (f, v1) ->
              T_machine.App2_2
                (dec_fun "App2_2 frame fun" rho f,
                 dec_int "App2_2 frame v1" rho v1)
          | Points.FApp3_1 (f, e2, e3) ->
              T_machine.App3_1
                (dec_fun "App3_1 frame fun" rho f,
                 dec_expr "App3_1 frame e2" rho e2,
                 dec_expr "App3_1 frame e3" rho e3)
          | Points.FApp3_2 (f, v1, e3) ->
              T_machine.App3_2
                (dec_fun "App3_2 frame fun" rho f,
                 dec_int "App3_2 frame v1" rho v1,
                 dec_expr "App3_2 frame e3" rho e3)
          | Points.FApp3_3 (f, v1, v2) ->
              T_machine.App3_3
                (dec_fun "App3_3 frame fun" rho f,
                 dec_int "App3_3 frame v1" rho v1,
                 dec_int "App3_3 frame v2" rho v2)
          | Points.FRestore env ->
              T_machine.Restore (dec_env "Restore frame" rho env)
          | Points.FIfz (e2, e3) ->
              T_machine.Ifz (dec_expr "Ifz frame then" rho e2,
                             dec_expr "Ifz frame else" rho e3)
          | Points.FSilent -> T_machine.Silent
        in
        Some f

  (* Decode an S continuation to a T continuation, dropping unobserved frames.
     Order is preserved: both are innermost-frame-first. *)
  let kont (p : Points.t) (k : S_cek.kont) : T_machine.kont =
    List.filter_map (frame p) k

  (* Decode an observed S state to a T state. Returns [None] for an unobserved
     state. At the eval entry the control is the decoded [e]; at an eval return
     it is the raw integer in the return variable. *)
  let state (p : Points.t) (s : S_cek.state) : T_machine.state option =
    if Label.equal s.S_cek.label p.Points.eval_entry then
      Some
        {
          T_machine.control =
            T_machine.Expr (dec_expr "eval entry control" s.S_cek.env p.Points.eval_e);
          env = dec_env "eval entry env" s.S_cek.env p.Points.eval_env;
          kont = kont p s.S_cek.kont;
        }
    else
      match Points.ret_var p s.S_cek.label with
      | None -> None
      | Some r ->
          Some
            {
              T_machine.control = T_machine.Value (dec_int "eval return control" s.S_cek.env r);
              env = dec_env "eval return env" s.S_cek.env p.Points.eval_env;
              kont = kont p s.S_cek.kont;
            }
end

(** {1 S trace capture} *)

(** The full sequence of S states of [I_S^T] run on the encoded T program [prog]
    with top-level argument [arg], seeded as in {!Interp_st.eval_t} and including
    the final state. [fuel] guards against a non-terminating run. *)
let s_trace ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : S_cek.state list =
  let env =
    S_cek.Env.add Interp_st.arg_p (T_encoding.enc_program prog)
      (S_cek.Env.add Interp_st.arg_arg (T_encoding.enc_value arg)
         S_cek.Env.empty)
  in
  let init = S_cek.inject ~env Interp_st.program in
  let rec loop n s acc =
    if n <= 0 then failwith "Projection.s_trace: step budget exhausted"
    else
      match S_cek.step Interp_st.program s with
      | S_cek.Done _ -> List.rev (s :: acc)
      | S_cek.Next s' -> loop (n - 1) s' (s :: acc)
  in
  loop fuel init []

(** {1 Projected trace} *)

(** The projected T trace: the definition table the T machine runs against and
    the sequence of decoded T states at observed interpreter points. *)
type projected = { defs : T_encoding.defs; states : T_machine.state list }

(** The interpreter points of [I_S^T], computed once. *)
let points : Points.t = Points.extract ()

(** Project an S trace: keep observed states, decode each to a T state. *)
let project_states (trace : S_cek.state list) : T_machine.state list =
  List.filter_map (Decode.state points) trace

(** Run [I_S^T] on [prog] and project the resulting S trace to a T trace. *)
let project ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : projected =
  let trace = s_trace ~fuel ~arg prog in
  { defs = prog.T_encoding.defs; states = project_states trace }

(** {1 Verification} *)

(** Outcome of verifying a projected trace against the T machine. *)
type result =
  | Valid  (** every consecutive pair is connected by one {!T_machine.step} *)
  | Empty  (** the projected trace had no observed states *)
  | Mismatch of {
      index : int;
      from_state : T_machine.state;
      expected : T_machine.state option;
          (** the T-machine successor of [from_state], or [None] if [from_state]
              steps to a final value *)
      got : T_machine.state;  (** the next decoded state in the projected trace *)
    }

(** Verify that a projected T trace is a valid run of the T machine: each
    consecutive pair of decoded states must be connected by exactly one
    {!T_machine.step}. This is the executable form of the macro-step
    bisimulation: one T step per macro group of S steps. *)
let verify (pr : projected) : result =
  let arr = Array.of_list pr.states in
  let n = Array.length arr in
  if n = 0 then Empty
  else
    let rec loop i =
      if i + 1 >= n then Valid
      else
        let cur = arr.(i) in
        let next = arr.(i + 1) in
        match T_machine.step pr.defs cur with
        | T_machine.Next expected when expected = next -> loop (i + 1)
        | T_machine.Next expected ->
            Mismatch
              { index = i; from_state = cur; expected = Some expected; got = next }
        | T_machine.Done _ ->
            Mismatch { index = i; from_state = cur; expected = None; got = next }
    in
    loop 0

(** Run [I_S^T] on [prog], project, and verify in one call. *)
let verify_program ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : result =
  verify (project ~fuel ~arg prog)

(** {1 Cross-check against the T machine's own run} *)

(** The full state sequence of the T machine on [prog] (including the final value
    state with the empty continuation), the direct analogue of the projected
    trace. *)
let t_trace ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : T_machine.state list =
  let init = T_machine.inject ~arg prog in
  let rec loop n s acc =
    if n <= 0 then failwith "Projection.t_trace: step budget exhausted"
    else
      match T_machine.step prog.T_encoding.defs s with
      | T_machine.Done _ -> List.rev (s :: acc)
      | T_machine.Next s' -> loop (n - 1) s' (s :: acc)
  in
  loop fuel init []

(** Whether the projected trace of [prog] equals the T machine's own trace. This
    is a single equality of decoded T-state lists; when it holds, the projection
    is not merely {e a} valid T run but {e the} canonical one. *)
let equals_t_machine ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : bool =
  (project ~fuel ~arg prog).states = t_trace ~fuel ~arg prog
