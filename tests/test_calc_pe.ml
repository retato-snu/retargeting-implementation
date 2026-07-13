(* Gates: is the specialized analyzer the mechanical PE image of the base
   analyzer?

   Calc_pe derives, from the interpreter text alone (plus the Role_pe
   auxiliary certificate), a specialized residual of the base analyzer:
   segments between the cuts its own data dependencies force. The gates:

   Segmentation: the derived segment set IS the paper's tab:macro — the cut
      labels coincide with {match} ∪ L_ret (plus main's return) and L_call,
      and every segment chain matches the paper's factorization row (modulo
      the impl's extra [x0] glue in App2/Init, asserted explicitly).

   Decode support: the per-frame live sets coincide with the paper's context
      bindings β_ℓ up to the interpreter's env/defs threading; the Restore
      payload is the documented delta (the paper threads ρ through the state,
      licensed by lem:brack — the S image reads the caller's saved env
      instead, so its live set is empty).

   Behavior: on the shared suite, the specialized lanes terminate, are sound
      against the concrete T machine (exact and unknown arguments), the
      residual's table lives ONLY on the derived cut points (the specialized
      analyzer's state space: Entry/Ret/Frame), the retargeted continuation
      index is inert (• everywhere — its only producers were the auxiliary
      calls folded into denotations), and the pop counts collapse from the
      base's per-S-label scale to the per-T-rule scale (compared against
      the base's per-S-label scale). *)

open Retargeting
open Test_util
module DV = Calc_pe.Derive

let seg (segs : DV.segment list) (name : string) : DV.segment =
  match List.find_opt (fun (s : DV.segment) -> String.equal s.DV.name name) segs with
  | Some s -> s
  | None ->
      Printf.printf "FAIL - calc_pe: no derived segment named %s\n" name;
      exit 1

let run () =
  banner
    "== calc_pe: the specialized analyzer as the partial-evaluation image of \
     the base analyzer ==";

  (* ------------------------------------------------------------------ segmentation *)
  let segs = DV.derive () in
  Printf.printf "   derived segmentation (the mechanical tab:macro):\n";
  List.iter (fun s -> Printf.printf "     %s\n" (DV.string_of_segment s)) segs;

  (* init + 13 entry (Int/Var/Add/Sub/Mul/Div/Mod/Lt/Let/App/App2/App3/Ifz) + 28
     resume (each of the 6 binary ops contributes #1/#2 = 12; Let/App contribute
     #1/#2 = 4; App2 contributes #1/#2/#3 = 3 and App3 #1/#2/#3/#4 = 4 — one
     resume per operand + the body eval; Ifz contributes #1/True, #1/False, #2,
     #3 = 4; plus resume@root = 1). *)
  check "42 segments derived (init + 13 entry + 28 resume)"
    (List.length segs = 42);

  (* the derived cuts coincide with the paper's observation/call labels *)
  let pts = Projection.points in
  let ret_ls =
    List.map fst pts.Projection.Points.ret_labels |> Label.Set.of_list
  in
  let call_ls =
    List.map fst pts.Projection.Points.call_frames |> Label.Set.of_list
  in
  let derived_rets =
    List.filter_map
      (fun (s : DV.segment) ->
        match s.DV.stop with DV.TabulateRet l -> Some l | _ -> None)
      segs
    |> Label.Set.of_list
  in
  let derived_entries =
    List.filter_map
      (fun (s : DV.segment) ->
        match s.DV.stop with DV.EnterEval l -> Some l | _ -> None)
      segs
    |> Label.Set.of_list
  in
  let root_site =
    match (seg segs "resume@root").DV.site with
    | Some l -> l
    | None -> -1
  in
  let derived_sites =
    List.filter_map (fun (s : DV.segment) -> s.DV.site) segs
    |> List.filter (fun l -> not (Label.equal l root_site))
    |> Label.Set.of_list
  in
  let main_ret =
    match (seg segs "resume@root").DV.stop with
    | DV.TabulateRet l -> l
    | _ -> -1
  in
  check "derived return cuts = paper L_ret ∪ {main return}"
    (Label.Set.equal derived_rets (Label.Set.add main_ret ret_ls));
  check "derived entry cut = paper eval-entry (match)"
    (Label.Set.equal derived_entries
       (Label.Set.singleton pts.Projection.Points.eval_entry));
  check "derived frame sites = paper L_call"
    (Label.Set.equal derived_sites call_ls);

  (* each derived chain = the paper's tab:macro factorization row.
     Two rows carry impl glue the paper's listing does not have: App2 and
     Init each pass through one extra S-LetExp (the [x0 = 0] binding of the
     implicit parameter id); asserted here as the exact expected delta. *)
  let expect name shape stop reads =
    let s = seg segs name in
    check (name ^ " chain") (DV.shape s = shape);
    (match (s.DV.stop, stop) with
    | DV.TabulateRet _, `Ret | DV.EnterEval _, `Eval ->
        check (name ^ " stop") true
    | _ -> check (name ^ " stop") false);
    check (name ^ " live set")
      (DV.SS.equal s.DV.reads (DV.SS.of_list reads))
  in
  (* T-Init (paper: LetCall; impl main glue: Match;LetExp;LetExp;extend) *)
  expect "init" [ "Match"; "LetExp"; "LetExp"; "aux:extend"; "LetCall" ] `Eval [];
  (* T-Int / T-Var *)
  expect "entry/Int" [ "Match"; "LetExp" ] `Ret [];
  expect "entry/Var" [ "Match"; "aux:lookup" ] `Ret [];
  (* T-Sub1 / T-Mul1 / T-Let1 / T-App1 / T-Ifz1 *)
  expect "entry/Sub" [ "Match"; "LetCall" ] `Eval [];
  expect "entry/Mul" [ "Match"; "LetCall" ] `Eval [];
  expect "entry/Let" [ "Match"; "LetCall" ] `Eval [];
  expect "entry/App" [ "Match"; "LetCall" ] `Eval [];
  expect "entry/Ifz" [ "Match"; "LetCall" ] `Eval [];
  (* T-Sub2 / T-Subr (β_sub1 = ⟨e2⟩ + env/defs threading; β_sub2 = ⟨v1⟩) *)
  expect "resume@Sub#1" [ "Return"; "LetCall" ] `Eval [ "e2"; "env"; "defs" ];
  expect "resume@Sub#2" [ "Return"; "LetExp" ] `Ret [ "v1" ];
  expect "resume@Mul#1" [ "Return"; "LetCall" ] `Eval [ "e2"; "env"; "defs" ];
  expect "resume@Mul#2" [ "Return"; "LetExp" ] `Ret [ "v1" ];
  (* T-Let2 (β_let1 = ⟨x, e2⟩ + threading) *)
  expect "resume@Let#1"
    [ "Return"; "aux:extend"; "LetCall" ]
    `Eval
    [ "env"; "x"; "e2"; "defs" ];
  (* T-Restore: the mechanical live set is EMPTY — the paper's β_let2 =
     Restore⟨env⟩ payload is not read by any transfer; the S image reinstates
     the caller's saved env through the return mechanics (lem:brack's
     state-threading is the hand step PE does not discover). *)
  expect "resume@Let#2" [ "Return" ] `Ret [];
  (* T-App2 (β_app1 = ⟨fid⟩ + defs; env is NOT live — fresh callee env);
     chain = paper row + one extra LetExp (the x0 glue). *)
  expect "resume@App#1"
    [ "Return"; "aux:fundef"; "LetExp"; "LetExp"; "aux:extend"; "LetCall" ]
    `Eval [ "defs"; "fid" ];
  expect "resume@App#2" [ "Return" ] `Ret [];
  (* T-Ifz2 / T-Ifz3 (β_ifz1 = ⟨e2, e3⟩ split across the two derived
     branches) and T-Silent *)
  expect "resume@Ifz#1/True"
    [ "Return"; "Match"; "LetCall" ]
    `Eval [ "e2"; "env"; "defs" ];
  expect "resume@Ifz#1/False"
    [ "Return"; "Match"; "LetCall" ]
    `Eval [ "e3"; "env"; "defs" ];
  expect "resume@Ifz#2" [ "Return" ] `Ret [];
  expect "resume@Ifz#3" [ "Return" ] `Ret [];
  expect "resume@root" [ "Return" ] `Ret [];

  (* ------------------------------------------------------------------ behavior *)
  banner "== calc_pe: behavior of the specialized lanes ==";

  let module D = Domain_rtg in
  let module A = S_abstract in
  let progs : (string * T_encoding.program) list =
    [
      ("(3-1)*2", arith);
      ("let x=5 in x-2", let_sub);
      ("sq(4)", sq4);
      ("ifz(3-3)", ifz_zero);
      ("ifz(3-1)", ifz_nonzero);
      ("let+call+sub", let_call_sub);
      ("nested sub", nested_sub);
      ("id", id_prog);
      ("ifz over arg", ifz_arg);
      ("recursive f", rec_fun);
      ( "even/odd",
        parse_t
          "e(n) = ifz n then 1 else o(n - 1); o(n) = ifz n then 0 else e(n - \
           1); e(x)" );
      ("power2", parse_t "f(n) = ifz n then 1 else 2 * f(n - 1); f(x)");
      ("call-chain", parse_t "f(x) = x - 1; g(x) = f(x) - 1; g(f(g(0)))");
    ]
  in
  let args = [ 0; 1; 3; 7 ] in

  (* the labels the residual is allowed to tabulate: the derived cuts *)
  let allowed_labels =
    let sites =
      List.filter_map (fun (s : DV.segment) -> s.DV.site) segs
      |> Label.Set.of_list
    in
    Label.Set.union derived_rets
      (Label.Set.union derived_entries
         (Label.Set.add Interp_st.program.S_syntax.main sites))
  in

  (* precision-relation counters vs the base (measured, not asserted) *)
  let n_below = ref 0 and n_equal = ref 0 and n_above = ref 0 and n_inc = ref 0 in
  let note_rel ?(who = "") ?(cell = "") (c : D.aint) (b : D.aint) : unit =
    let le = D.aint_leq c b and ge = D.aint_leq b c in
    if le && ge then incr n_equal
    else begin
      if le then incr n_below
      else if ge then incr n_above
      else incr n_inc;
      Printf.printf "   [rel] %s %s: %s vs %s (%s)\n" cell who
        (D.string_of_aint c) (D.string_of_aint b)
        (if le then "below" else if ge then "ABOVE" else "INCOMPARABLE")
    end
  in
  List.iter
    (fun (name, p) ->
      List.iter
        (fun arg ->
          let c = Calc_pe.analyze_t ~arg:(D.int_lit arg) p in
          let cd = Calc_pe.analyze_t_dis ~arg:(D.int_lit arg) p in
          let a = A.analyze_t ~arg:(D.int_lit arg) p in
          (match (try Some (T_machine.run ~arg p) with _ -> None) with
          | Some n ->
              check
                (Printf.sprintf "%s (arg=%d): specialized (retargeted domain) sound (mem %d)" name
                   arg n)
                (D.aint_mem n (D.root_int c.Calc_pe.result));
              check
                (Printf.sprintf "%s (arg=%d): specialized (disambiguated value domain) sound (mem %d)" name
                   arg n)
                (D.aint_mem n cd.Calc_pe.result)
          | None -> ());
          let cell = Printf.sprintf "%s(arg=%d)" name arg in
          note_rel ~who:"specialized vs base" ~cell
            (D.root_int c.Calc_pe.result)
            (D.root_int a.A.result);
          (* the residual's state space = the derived cut points only *)
          check
            (Printf.sprintf "%s (arg=%d): table on cut points only" name arg)
            (A.Table.for_all
               (fun (phi, _) _ ->
                 Label.Set.mem (Partition.lab phi) allowed_labels)
               c.Calc_pe.table);
          (* the retargeted continuation index is inert after folding the
             auxiliary calls *)
          check
            (Printf.sprintf "%s (arg=%d): kidx degenerate (• everywhere)" name
               arg)
            (A.Table.for_all
               (fun (_, k) _ -> A.compare_kidx k A.KBullet = 0)
               c.Calc_pe.table))
        args;
      (* the PURE-SPECIALIZATION arm (the auxiliary summary — no fold, no dis):
         sound, and never above the base at the root. Specializing through the
         aux bodies removes the intra-aux label pooling (the tuple-pooling
         point becomes an interior point of a segment), so this arm may be
         strictly MORE precise than the base, never less. *)
      List.iter
        (fun arg ->
          let ca = Calc_pe.analyze_t_analyzed ~arg:(D.int_lit arg) p in
          (match (try Some (T_machine.run ~arg p) with _ -> None) with
          | Some n ->
              check
                (Printf.sprintf "%s (arg=%d): specialized (summary) sound (mem %d)"
                   name arg n)
                (D.aint_mem n (D.root_int ca.Calc_pe.result))
          | None -> ());
          let b = A.analyze_t ~arg:(D.int_lit arg) p in
          check
            (Printf.sprintf "%s (arg=%d): specialized (summary) ⊑ base at the root"
               name arg)
            (D.aint_leq (D.root_int ca.Calc_pe.result) (D.root_int b.A.result)))
        args;
      (* unknown argument: soundness at every concrete argument's run *)
      let c_top = Calc_pe.analyze_t ~arg:D.any_int p in
      let cd_top = Calc_pe.analyze_t_dis ~arg:D.any_int p in
      let ca_top = Calc_pe.analyze_t_analyzed ~arg:D.any_int p in
      List.iter
        (fun arg ->
          match (try Some (T_machine.run ~arg p) with _ -> None) with
          | Some n ->
              check
                (Printf.sprintf "%s: specialized (retargeted domain) sound at unknown arg (mem %d)"
                   name n)
                (D.aint_mem n (D.root_int c_top.Calc_pe.result));
              check
                (Printf.sprintf "%s: specialized (disambiguated value domain) sound at unknown arg (mem %d)"
                   name n)
                (D.aint_mem n cd_top.Calc_pe.result);
              check
                (Printf.sprintf
                   "%s: specialized (summary) sound at unknown arg (mem %d)" name n)
                (D.aint_mem n (D.root_int ca_top.Calc_pe.result))
          | None -> ())
        args)
    progs;
  Printf.printf
    "   precision vs base at the integer root (%d cells): below %d, equal %d, \
     above %d, incomparable %d\n"
    (List.length progs * List.length args)
    !n_below !n_equal !n_above !n_inc;

  (* pop scale: the specialized lanes pop once per T-rule application per
     context; the base pops once per S-label entry. *)
  banner "== calc_pe: pop-count scale (base vs specialized vs disambiguated) ==";
  Printf.printf "   %-14s %8s %8s(-%s) %8s\n" "program" "base"
    "spec" "passive" "spec-dis";
  List.iter
    (fun (name, p) ->
      let arg = D.any_int in
      let _ = A.analyze_t ~arg p in
      let base_pops = !A.last_solve_steps in
      let _ = Calc_pe.analyze_t ~arg p in
      let c_pops, c_passive, _ = !Calc_pe.last_stats in
      let cd = Calc_pe.analyze_t_dis ~arg p in
      Printf.printf "   %-14s %8d %8d(-%d) %8d\n" name base_pops c_pops
        c_passive cd.Calc_pe.pops;
      (* the productive pops (T-rule applications per context) sit below the
         base's per-S-label pops — by the segment-length factor on ordinary
         rules, and by the collapsed auxiliary runs where those dominate *)
      check
        (Printf.sprintf "%s: productive specialized pops < base pops" name)
        (c_pops - c_passive < base_pops))
    [
      ("recursive f", rec_fun);
      ("power2", parse_t "f(n) = ifz n then 1 else 2 * f(n - 1); f(x)");
      ( "even/odd",
        parse_t
          "e(n) = ifz n then 1 else o(n - 1); o(n) = ifz n then 0 else e(n - \
           1); e(x)" );
      ("call-chain", parse_t "f(x) = x - 1; g(x) = f(x) - 1; g(f(g(0)))");
      ("nested sub", nested_sub);
      ( "call-chain 15",
        (* the aux-heavy scaling family: nested unary calls whose
           lookup/fundef spines dominate the base's pops; the auxiliary
           denotations collapse them (the only asymptotic pop reducer among
           the arms) *)
        let b = Buffer.create 256 in
        Buffer.add_string b "f1(x) = x - 1;\n";
        for i = 2 to 15 do
          Buffer.add_string b
            (Printf.sprintf "f%d(x) = f%d(x) - 1;\n" i (i - 1))
        done;
        Buffer.add_string b "f15(x)";
        parse_t (Buffer.contents b) );
    ];

  (* ------------------------------------------------------------------ role map *)
  (* The paper's role map has two forms: [Role.fields], the first-class table the
     disambiguated domain consumes, and [Role_pe.fields_of_tag], which the
     certificate recovers from the interpreter text. They are the same map, so
     they must agree tag for tag — and on EVERY tag the encoding has, or a new T
     form would silently reach the domain as an unkeyed junk flow. *)
  let role_of_pe : Role_pe.role -> Role.t option = function
    | Role_pe.Static_label -> Some Role.Label
    | Role_pe.Static_var -> Some Role.Var
    | Role_pe.Static_fun -> Some Role.Fname
    | Role_pe.Static_lit | Role_pe.Dyn_int -> Some Role.Num
    | Role_pe.Code -> Some Role.Exp
    | Role_pe.Env -> Some Role.Env
    | Role_pe.Defs -> Some Role.Fundef
    | Role_pe.Static_bool -> Some Role.Bool
    | Role_pe.Prog -> None
  in
  let tags =
    T_encoding.
      [ tag_int; tag_var; tag_add; tag_sub; tag_mul; tag_div; tag_mod; tag_lt;
        tag_let; tag_app; tag_app2; tag_app3; tag_ifz; tag_fun; tag_eof;
        tag_extend; tag_empty ]
  in
  List.iter
    (fun tg ->
      check
        (Printf.sprintf "role map: %s is keyed, and the two forms agree" tg)
        (match (Role.fields tg, Role_pe.fields_of_tag tg) with
        | Some rs, Some ps ->
            List.length rs = List.length ps
            && List.for_all2 (fun r p -> role_of_pe p = Some r) rs ps
        | _ -> false))
    tags;

  banner "calc_pe tests passed"
