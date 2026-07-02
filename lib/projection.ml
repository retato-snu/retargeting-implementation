(** Concrete S -> T projection at the level of machine states, with the macro-step bisimulation check (main.tex:536-612, 628-647, 1027-1038). *)

(** {1 Interpreter points} *)

module Points = struct
  (** The T continuation-frame role a recursive [eval] call site stands for (the paper's [β_ℓ], main.tex:573-597). *)
  type frame_kind =
    | FSub1 of S_syntax.var
    | FSub2 of S_syntax.var
    | FMul1 of S_syntax.var
    | FMul2 of S_syntax.var
    | FLet of S_syntax.var * S_syntax.var
    | FApp of S_syntax.var
    | FRestore of S_syntax.var
    | FIfz of S_syntax.var * S_syntax.var
    | FSilent

  type t = {
    eval_entry : Label.t;  (** eval-entry [match] label *)
    eval_e : S_syntax.var;  (** [eval]'s expression parameter *)
    eval_env : S_syntax.var;  (** [eval]'s environment parameter *)
    ret_labels : (Label.t * S_syntax.var) list;
    call_frames : (Label.t * frame_kind) list;
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

  let eval_branches (eval : S_syntax.fundef) (e : S_syntax.var) =
    match cmd_at eval.S_syntax.entry with
    | S_syntax.Match (a, branches) when is_var e a -> branches
    | _ -> fail "eval body must match its expression parameter"

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

    let () =
      let _vars, body = branch T_encoding.tag_var branches in
      match cmd_at body with
      | S_syntax.LetCall (_, f, _, k) when String.equal f Interp_st.f_lookup ->
          add_ret (expect_return "Var return" k)
      | _ -> fail "Var branch must call lookup then return"
    in

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
    binary T_encoding.tag_sub "sub" (fun e2 -> FSub1 e2) (fun v1 -> FSub2 v1);
    binary T_encoding.tag_mul "mul" (fun e2 -> FMul1 e2) (fun v1 -> FMul2 v1);

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

    let () =
      let vars, app_body = branch T_encoding.tag_app branches in
      let fvar, e1 =
        match vars with
        | [ _l; f; e1 ] -> (f, e1)
        | _ -> fail "App branch must bind label, function, argument"
      in
      let fun_body =
        match cmd_at app_body with
        | S_syntax.Match (a, fbranches) when is_var fvar a ->
            let _vars, l = branch T_encoding.tag_fun fbranches in
            l
        | _ -> fail "App branch must match its function value"
      in
      let call1, after1 = expect_eval_call "App argument" env defs e1 fun_body in
      add_call (call1, FApp fvar);
      let rec find_body_call l =
        match cmd_at l with
        | S_syntax.LetCall (_, f, [ a0; a1; a2 ], next)
          when String.equal f Interp_st.f_eval && is_var defs a2 ->
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

    let () =
      let vars, body = branch T_encoding.tag_ifz branches in
      let e1, e2, e3 =
        match vars with
        | [ _l; e1; e2; e3 ] -> (e1, e2, e3)
        | _ -> fail "Ifz branch must bind label and three subexpressions"
      in
      let call1, after1 = expect_eval_call "Ifz scrutinee" env defs e1 body in
      add_call (call1, FIfz (e2, e3));
      let bool_branches =
        match cmd_at after1 with
        | S_syntax.Match (S_syntax.EPrim ("iszero", _), bbranches) -> bbranches
        | _ -> fail "Ifz branch must match iszero(v1) directly"
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

  let ret_var (p : t) (l : Label.t) : S_syntax.var option =
    List.find_map
      (fun (rl, v) -> if Label.equal rl l then Some v else None)
      p.ret_labels

  let frame_kind (p : t) (l : Label.t) : frame_kind option =
    List.find_map
      (fun (cl, fk) -> if Label.equal cl l then Some fk else None)
      p.call_frames

  let is_observed (p : t) (l : Label.t) : bool =
    Label.equal l p.eval_entry || ret_var p l <> None
end

(** {1 State decoding} *)

module Decode = struct
  exception Project_error of string

  let fail fmt = Printf.ksprintf (fun s -> raise (Project_error s)) fmt

  let read (ctx : string) (rho : S_cek.env) (x : S_syntax.var) : S_cek.value =
    match S_cek.Env.find_opt x rho with
    | Some v -> v
    | None -> fail "%s: variable %s not bound" ctx x

  let dec_expr ctx rho x = T_encoding.dec_expr (read ctx rho x)
  let dec_env ctx rho x = T_encoding.dec_env (read ctx rho x)
  let dec_var ctx rho x = T_encoding.dec_var_id ctx (read ctx rho x)
  let dec_fun ctx rho x = T_encoding.dec_fun_id ctx (read ctx rho x)

  let dec_int ctx rho x =
    match read ctx rho x with
    | S_cek.VInt n -> n
    | S_cek.VTag (t, _) -> fail "%s: expected an integer, got tag %s" ctx t

  (* Auxiliary and root frames (non-eval-calls) decode to [None] (main.tex:558, 616-619). *)
  let frame (p : Points.t) (fr : S_cek.frame) : T_machine.frame option =
    match Points.frame_kind p fr.S_cek.suspended with
    | None -> None
    | Some fk ->
        let rho = fr.S_cek.saved_env in
        let f =
          match fk with
          | Points.FSub1 e2 -> T_machine.Sub1 (dec_expr "Sub1 frame" rho e2)
          | Points.FSub2 v1 -> T_machine.Sub2 (dec_int "Sub2 frame" rho v1)
          | Points.FMul1 e2 -> T_machine.Mul1 (dec_expr "Mul1 frame" rho e2)
          | Points.FMul2 v1 -> T_machine.Mul2 (dec_int "Mul2 frame" rho v1)
          | Points.FLet (x, e2) ->
              T_machine.Let (dec_var "Let frame var" rho x,
                             dec_expr "Let frame body" rho e2)
          | Points.FApp f -> T_machine.App (dec_fun "App frame" rho f)
          | Points.FRestore env ->
              T_machine.Restore (dec_env "Restore frame" rho env)
          | Points.FIfz (e2, e3) ->
              T_machine.Ifz (dec_expr "Ifz frame then" rho e2,
                             dec_expr "Ifz frame else" rho e3)
          | Points.FSilent -> T_machine.Silent
        in
        Some f

  (* Order preserved: both continuations are innermost-frame-first. *)
  let kont (p : Points.t) (k : S_cek.kont) : T_machine.kont =
    List.filter_map (frame p) k

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

(** Full sequence of S states from running [I_S^T] on the encoded program [prog]. *)
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

(** The projected T trace: definition table plus decoded T states at observed points. *)
type projected = { defs : T_encoding.defs; states : T_machine.state list }

let points : Points.t = Points.extract ()

let project_states (trace : S_cek.state list) : T_machine.state list =
  List.filter_map (Decode.state points) trace

let project ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : projected =
  let trace = s_trace ~fuel ~arg prog in
  { defs = prog.T_encoding.defs; states = project_states trace }

(** {1 Verification} *)

type result =
  | Valid  (** every consecutive pair is connected by one {!T_machine.step} *)
  | Empty  (** the projected trace had no observed states *)
  | Mismatch of {
      index : int;  (** the position of the offending state in the trace *)
      from_state : T_machine.state;  (** the decoded state to step from *)
      expected : T_machine.state option;
      got : T_machine.state;  (** the next decoded state in the projected trace *)
    }

(** Verify a projected T trace is a valid T-machine run: one {!T_machine.step} per consecutive pair — the executable macro-step bisimulation (main.tex:1027-1038). *)
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

let verify_program ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : result =
  verify (project ~fuel ~arg prog)

(** {1 Cross-check against the T machine's own run} *)

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

let equals_t_machine ?(fuel = 1_000_000) ?(arg : T_encoding.value = 0)
    (prog : T_encoding.program) : bool =
  (project ~fuel ~arg prog).states = t_trace ~fuel ~arg prog
