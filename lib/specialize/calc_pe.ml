(** The in-process reference implementation of the paper's specialized analyzer:
    the calculated transfer [F_⟦T⟧], the base analyzer's micro-transfers composed
    along the segments the base's own table reads force. The paper calculates a
    T-CEK machine from [I_S^T] (§sec:calc), grouping the S micro-steps between
    consecutive observed states into one macro-step per T rule (tab:macro); its
    hand-written macro engine is that machine's abstract interpretation. Here the
    same shape is derived instead, from {!S_abstract} and the interpreter {e text}
    alone — {!Interp_st.program}, the auxiliary certificate
    {!Role_pe.certify_interp_st} (def:auxfam), and a domain carrying the certified
    auxiliary denotations (def:auxop) — with the T program as analysis data and no
    tab:macro row or observation-label set copied in.

    The {e cut criterion} is not the paper's [L_obs] but a consequence of the base
    transfer's data dependencies: a successor needing no table read is inlined
    ([AbsLetExp], [AbsMatch], and a certified auxiliary call folded to its
    denotation); a non-auxiliary call must tabulate the caller frame (read back by
    [AbsReturn]'s precise lookup) and the callee entry (reached through the stored
    continuation linkage); and a [Return]'s successors depend on the dynamically
    accumulated continuation set, so it too is tabulated, popped later. The cuts
    come out as exactly [{match} ∪ L_ret] plus [L_call], so the residual table
    holds eval entries, eval returns and call-site frames — the calculated
    machine's point space — and {!Derive} prints the derived chains (tab:macro)
    and frame live sets (the support of [β_ℓ]).

    Everything else is the base's code: plugged into {!S_abstract.Make.solve} via
    [~step], the step inherits the table and its [(Partition, kidx)] keys,
    [update]'s join-or-widen, [refine_succ]'s scope write-back, the worklist order
    and the reverse dependency index, and within a segment it performs exactly the
    domain operations of the matching {!S_abstract.step_entry} arms, in order.

    Not claimed: context sensitivity is inherited from the base (callee entries
    join over callers), so only the machine {e shape} is reproduced, at base
    sensitivity; and the paper's machine threads the environment through the
    {e state} and restores it via [Restore] frames, where the image reads it from
    the caller's {e saved} environment — the two agree by well-bracketedness
    (lem:brack), a step supplied by hand, not discovered by the composition. *)

module S = S_syntax

(** {1 The certified auxiliary family}

    The auxiliary functions whose calls fold to denotations, read off the
    {!Role_pe} certificate — the textual witness for def:auxfam. *)

let certified_aux_names () : string list =
  match Role_pe.certify_interp_st () with
  | Error msgs ->
      failwith
        ("Calc_pe: auxiliary family not certified: " ^ String.concat "; " msgs)
  | Ok cert ->
      List.map (fun (a : Role_pe.aux_summary) -> a.Role_pe.name) cert.Role_pe.aux

(** {1 Symbolic derivation: segments, chains, live sets}

    The same cut criterion as the abstract walk, run over the text with no
    domain: it enumerates every segment and records the chain of S rules
    traversed (the derived tab:macro row) and, for resume segments, the
    caller-saved variables read (the derived [β_ℓ] support). *)

module Derive = struct
  module SS = Set.Make (String)

  (** One S micro-step (or folded auxiliary macro-step) of a segment chain. *)
  type stepk =
    | KReturn  (** the S-Return that starts every resume segment *)
    | KMatch of Label.t * S.tag  (** S-Match dispatch, the branch taken *)
    | KLetExp of Label.t  (** S-LetExp glue *)
    | KAuxFold of Label.t * string  (** a folded auxiliary macro-step *)
    | KPush of Label.t * string  (** S-LetCall: push the frame, enter callee *)

  (** Where a segment starts. *)
  type start =
    | SInit  (** the initial state (the entry command of [main]) *)
    | SEntry of S.tag  (** the eval-entry dispatch on one T-node tag *)
    | SResume of Label.t * S.tag option
        (** a return resuming the frame at call site [ℓ↓]; [Some tag] when an
            interior match (the [iszero] split) chose branch [tag] *)

  (** Where a segment stops — the derived cuts. *)
  type stop =
    | EnterEval of Label.t  (** enters the callee's entry (an observed entry) *)
    | TabulateRet of Label.t  (** reaches a [Return] command (an observed return) *)

  type segment = {
    name : string;  (** mechanical name: entry/<tag>, resume\@<tag>#<i>, init *)
    start : start;
    chain : stepk list;
    stop : stop;
    reads : SS.t;
        (** for resume segments: the caller-saved variables read along the walk —
            the live support of the frame payload ([β_ℓ] plus threading) *)
    site : Label.t option;  (** the call-site label for resume segments *)
  }

  let free_vars (e : S.exp) : SS.t =
    let rec go acc = function
      | S.EInt _ -> acc
      | S.EVar x -> SS.add x acc
      | S.EPrim (_, es) | S.ETag (_, _, es) -> List.fold_left go acc es
    in
    go SS.empty e

  let add_reads (local : SS.t) (reads : SS.t) (vs : SS.t) : SS.t =
    SS.union reads (SS.diff vs local)

  (** All maximal paths from [l] to a cut, tracking bound-vs-read variables: aux
      calls fold, a non-aux call or a [Return] is a cut. *)
  let rec paths (prog : S.program) (aux : string list) (local : SS.t)
      (reads : SS.t) (chain : stepk list) (l : Label.t) :
      (stepk list * stop * SS.t) list =
    match S.cmd_at prog l with
    | S.Return _ -> [ (List.rev chain, TabulateRet l, reads) ]
    | S.Let (x, e, k) ->
        let reads = add_reads local reads (free_vars e) in
        paths prog aux (SS.add x local) reads (KLetExp l :: chain) k
    | S.LetCall (x, f, args, k) ->
        let reads =
          List.fold_left
            (fun r a -> add_reads local r (free_vars a))
            reads args
        in
        if List.exists (String.equal f) aux then
          paths prog aux (SS.add x local) reads (KAuxFold (l, f) :: chain) k
        else
          let entry =
            match
              List.find_opt
                (fun (d : S.fundef) -> String.equal d.S.name f)
                prog.S.funs
            with
            | Some d -> d.S.entry
            | None -> -1
          in
          [ (List.rev (KPush (l, f) :: chain), EnterEval entry, reads) ]
    | S.Match (e, branches) ->
        let reads = add_reads local reads (free_vars e) in
        List.concat_map
          (fun (S.PTag (tag, vars), k) ->
            paths prog aux
              (List.fold_left (fun s v -> SS.add v s) local vars)
              reads
              (KMatch (l, tag) :: chain)
              k)
          branches

  (** The non-auxiliary call sites of a function body, in control order, each
      tagged with the eval-dispatch arm it belongs to (the [<tag>#<i>] naming). *)
  let call_sites (prog : S.program) (aux : string list) (entry : Label.t) :
      (Label.t * string) list =
    let seen = ref Label.Set.empty in
    let out = ref [] in
    let rec go (ctx : string) (l : Label.t) : unit =
      if not (Label.Set.mem l !seen) then begin
        seen := Label.Set.add l !seen;
        match S.cmd_at prog l with
        | S.Return _ -> ()
        | S.Let (_, _, k) -> go ctx k
        | S.LetCall (_, f, _, k) ->
            if not (List.exists (String.equal f) aux) then
              out := (l, ctx) :: !out;
            go ctx k
        | S.Match (_, branches) ->
            List.iter
              (fun (S.PTag (tag, _), k) ->
                go (if String.equal ctx "" then tag else ctx) k)
              branches
      end
    in
    go "" entry;
    List.rev !out

  (** Every segment of the interpreter program: the init segment, one per
      eval-dispatch branch, and the resume segments of every non-auxiliary call
      site (in [eval]'s body and in [main]). *)
  let derive () : segment list =
    let prog = Interp_st.program in
    let aux = certified_aux_names () in
    let eval =
      match
        List.find_opt
          (fun (d : S.fundef) -> String.equal d.S.name Interp_st.f_eval)
          prog.S.funs
      with
      | Some d -> d
      | None -> failwith "Calc_pe.Derive: no eval function"
    in
    (* init: from main's entry command (seeded vars are main's "formals") *)
    let init_segs =
      List.map
        (fun (chain, stop, reads) ->
          {
            name = "init";
            start = SInit;
            chain;
            stop;
            reads;
            site = None;
          })
        (paths prog aux
           (SS.of_list [ Interp_st.arg_p; Interp_st.arg_arg ])
           SS.empty [] prog.S.main)
    in
    (* entry segments: one per eval-dispatch branch; the walk starts at the
       Match command itself, so the branch tag names the segment *)
    let entry_segs =
      List.map
        (fun (chain, stop, reads) ->
          let tag =
            match chain with
            | KMatch (_, t) :: _ -> t
            | _ -> "?"
          in
          {
            name = "entry/" ^ tag;
            start = SEntry tag;
            chain;
            stop;
            reads;
            site = None;
          })
        (paths prog aux
           (SS.of_list eval.S.params)
           SS.empty [] eval.S.entry)
    in
    (* resume segments: from each non-aux call site's continuation, with the
       call's result variable bound by the S-Return that starts the segment *)
    let numbered (sites : (Label.t * string) list) : (Label.t * string) list =
      let counts = Hashtbl.create 8 in
      List.map
        (fun (l, tag) ->
          let n =
            match Hashtbl.find_opt counts tag with Some n -> n + 1 | None -> 1
          in
          Hashtbl.replace counts tag n;
          (l, Printf.sprintf "%s#%d" tag n))
        sites
    in
    let resume_of (l : Label.t) (nm : string) : segment list =
      match S.cmd_at prog l with
      | S.LetCall (x, _, _, k) ->
          List.map
            (fun (chain, stop, reads) ->
              let branch =
                List.find_map
                  (function KMatch (_, t) -> Some t | _ -> None)
                  chain
              in
              {
                name =
                  ("resume@" ^ nm
                  ^ match branch with Some t -> "/" ^ t | None -> "");
                start = SResume (l, branch);
                chain = KReturn :: chain;
                stop;
                reads;
                site = Some l;
              })
            (paths prog aux (SS.singleton x) SS.empty [] k)
      | _ -> []
    in
    let eval_sites = numbered (call_sites prog aux eval.S.entry) in
    let main_sites =
      List.map (fun (l, _) -> (l, "root")) (call_sites prog aux prog.S.main)
    in
    let resume_segs =
      List.concat_map (fun (l, nm) -> resume_of l nm) (eval_sites @ main_sites)
    in
    init_segs @ entry_segs @ resume_segs

  (** {2 Printing} *)

  let string_of_stepk = function
    | KReturn -> "Return"
    | KMatch (l, t) -> Printf.sprintf "Match@%d[%s]" l t
    | KLetExp l -> Printf.sprintf "LetExp@%d" l
    | KAuxFold (l, f) -> Printf.sprintf "aux(%s)@%d" f l
    | KPush (l, f) -> Printf.sprintf "LetCall@%d->%s" l f

  let string_of_stop = function
    | EnterEval l -> Printf.sprintf "=> enter eval@%d" l
    | TabulateRet l -> Printf.sprintf "=> tabulate ret@%d" l

  let string_of_segment (s : segment) : string =
    Printf.sprintf "%-16s %s %s%s" s.name
      (String.concat " ; " (List.map string_of_stepk s.chain))
      (string_of_stop s.stop)
      (if SS.is_empty s.reads then ""
       else "   reads{" ^ String.concat "," (SS.elements s.reads) ^ "}")

  (** The chain shape without labels — the comparison form the tests assert
      against the paper's tab:macro rows. *)
  let shape (s : segment) : string list =
    List.map
      (function
        | KReturn -> "Return"
        | KMatch _ -> "Match"
        | KLetExp _ -> "LetExp"
        | KAuxFold (_, f) -> "aux:" ^ f
        | KPush _ -> "LetCall")
      s.chain
end

(** {1 The label-role classifier — one text function for the cut criterion}

    Every transfer variant reads the role of a label off this one classifier, so
    the cut criterion lives in exactly one place. [is_aux] is the configuration's
    auxiliary predicate (a folded call site is inlined, never a cut) and [heads]
    the chain-start overlay ({!heads_of}). *)
type site_role =
  | Head        (** a chain start: [main] or a non-aux callee entry *)
  | Return_cut  (** a [Return]: a tabulated cut whose pop resumes callers *)
  | Frame_cut   (** a non-aux [LetCall]: a tabulated caller frame, read by
                    AbsReturn, popped passively *)
  | Aux_call    (** an aux [LetCall]: folded to a denotation, inlined — no cut *)
  | Interior    (** a non-head [Let]/[Match]: a straight-line interior —
                    leaked under the paper-faithful transfer, untabulated
                    under the cut-limited transfer *)

(** The role of a command, ignoring head-ness ({!site_role} overlays that). *)
let role_of_cmd (is_aux : S.var -> bool) : S.cmd -> site_role = function
  | S.Return _ -> Return_cut
  | S.LetCall (_, f, _, _) -> if is_aux f then Aux_call else Frame_cut
  | S.Let _ | S.Match _ -> Interior

(** The role of a label: a head if it starts a chain, else its command role. *)
let site_role (is_aux : S.var -> bool) (heads : Label.Set.t) (prog : S.program)
    (l : Label.t) : site_role =
  if Label.Set.mem l heads then Head else role_of_cmd is_aux (S.cmd_at prog l)

(** The chain-start labels under [is_aux]: [main] plus the entry of every fundef
    not folded away — only [eval] with the auxiliary denotations, every fundef
    entry when the auxiliaries are analyzed instead. Yields both {!heads_fold}
    and {!heads_analyzed}. *)
let heads_of (is_aux : S.var -> bool) (prog : S.program) : Label.Set.t =
  Label.Set.of_list
    (prog.S.main
    :: List.filter_map
         (fun (d : S.fundef) ->
           if is_aux d.S.name then None else Some d.S.entry)
         prog.S.funs)

(** {1 The specialized abstract step}

    The same walk as {!Derive}, executed over abstract values with the base's own
    building blocks: one worklist pop of a tabulated entry runs a whole segment. *)

module MakeA
    (D : Domain_intf.DOMAIN)
    (A : module type of S_abstract.Make (D)) =
struct
  (** How a certified auxiliary call is summarized inside a segment: [Fold] is
      the closed-form abstract denotation Â⟦f⟧ ({!Domain_rtg.aux_denot} /
      {!Domain_dis.Make.aux_denot}), a different computation than the base's,
      licensed by its soundness lemma (def:auxop, lem:auxdenote). *)
  type aux_impl = Fold of (S.var -> D.t list -> D.t option)
  type config = { aux_names : string list; aux_impl : aux_impl }

  (** Pops of tabulated caller frames: no-ops (their action was inlined into the
      segment that wrote them), counted so the pop metric can isolate the
      productive T-rule applications. *)
  let last_passive_pops : int ref = ref 0

  let is_aux (cfg : config) (f : S.var) : bool =
    List.exists (String.equal f) cfg.aux_names

  (* The composition of the base's micro-transfers along one segment, from label
     [l] under environment [rho], continuation index [k] and stored continuation
     set [kont]. [actx] is recomputed at each interior label from the would-be
     key of that label, exactly as the composition of per-label pops would.
     Successors accumulate in reverse and are reversed by the caller. *)
  let rec walk (cfg : config) (h : A.handle) (k : A.kidx) (kont : A.kont)
      (l : Label.t) (rho : A.aenv) (acc : A.succ list) : A.succ list =
    let actx () = A.actx_of (A.partition_of h l rho) k in
    match S.cmd_at h.A.prog l with
    | S.Return _ ->
        (* cut: tabulate the observed return state *)
        List.fold_left
          (fun acc (phi', rho') -> ((phi', k), rho', kont) :: acc)
          acc
          (A.partitions_of h l rho)
    | S.Let (x, e, cont) -> (
        (* [AbsLetExp], inlined *)
        match A.abs_exp ~actx:(actx ()) rho e with
        | None -> acc
        | Some v -> walk cfg h k kont cont (A.aenv_add x v rho) acc)
    | S.LetCall (x, f, args, cont) -> (
        match A.abs_exps ~actx:(actx ()) rho args with
        | None -> acc
        | Some arg_vals ->
            if is_aux cfg f then
              (* the auxiliary macro-step (lem:auxdenote); an undefined summary
                 is a delimited run reaching no observed state — no successor *)
              let v_opt =
                match cfg.aux_impl with Fold denot -> denot f arg_vals
              in
              match v_opt with
              | None -> acc
              | Some v -> walk cfg h k kont cont (A.aenv_add x v rho) acc
            else
              (* cut: [AbsLetCall] — tabulate the caller frame (the T frame that
                 [β_ℓ] decodes, read back by the resume's lookup) and the callee
                 entry, linked by the stored caller part *)
              match A.find_fun h f with
              | None -> acc
              | Some def ->
                  if List.length def.S.params <> List.length arg_vals then acc
                  else
                    let phi_l = A.partition_of h l rho in
                    let acc = ((phi_l, k), rho, kont) :: acc in
                    let callee_rho =
                      List.fold_left2
                        (fun e p v -> A.aenv_add p v e)
                        A.aenv_empty def.S.params arg_vals
                    in
                    let kidx' = A.push h phi_l def k in
                    let callee_kont =
                      [ A.KPart { A.pphi = phi_l; A.pkont = k } ]
                    in
                    List.fold_left
                      (fun acc (phi', rho') ->
                        ((phi', kidx'), rho', callee_kont) :: acc)
                      acc
                      (A.partitions_of h def.S.entry callee_rho))
    | S.Match (e, branches) -> (
        (* [AbsMatch], inlined: every feasible branch continues the walk *)
        match A.abs_exp ~actx:(actx ()) rho e with
        | None -> acc
        | Some scrut ->
            List.fold_left
              (fun acc (S.PTag (tag, vars), cont) ->
                let arity = List.length vars in
                if D.has_tag tag scrut then
                  match D.fields tag arity scrut with
                  | Some tuples ->
                      List.fold_left
                        (fun acc tuple ->
                          if List.length tuple = arity then
                            let rho' =
                              List.fold_left2
                                (fun e y v -> A.aenv_add y (D.gc v) e)
                                rho vars tuple
                            in
                            walk cfg h k kont cont rho' acc
                          else acc)
                        acc tuples
                  | None -> acc
                else acc)
              acc branches)

  (** The specialized per-entry step, a drop-in for {!S_abstract.Make.solve}'s
      [~step]. The popped key's command classifies the tabulated state: a
      [Match]/[Let] is a segment head (an eval-entry dispatch or the initial
      [main] state) and runs its segment; a [Return] is an observed return, and
      fuses [AbsReturn]'s precise caller lookup with the resume segment of the
      caller's call site; a [LetCall] is a tabulated caller frame, passive
      because its push was inlined into the segment that wrote it. *)
  let step (cfg : config) (h : A.handle) (sigma : A.state)
      ((phi, k) : A.Key.t) (rho : A.aenv) (kont : A.kont) : A.succ list =
    let l = Partition.lab phi in
    match S.cmd_at h.A.prog l with
    | S.Match _ | S.Let _ -> List.rev (walk cfg h k kont l rho [])
    | S.LetCall _ ->
        incr last_passive_pops;
        []
    | S.Return a -> (
        match A.abs_exp ~actx:(A.actx_of phi k) rho a with
        | None -> []
        | Some v ->
            List.rev
              (List.fold_left
                 (fun acc (e : A.kelem) ->
                   match e with
                   | A.KEmpty -> acc
                   | A.KPart caller -> (
                       let phi_c = caller.A.pphi and kidx_c = caller.A.pkont in
                       match S.cmd_at h.A.prog (Partition.lab phi_c) with
                       | S.LetCall (x, _f, _args, cont) -> (
                           match A.Table.find_opt (phi_c, kidx_c) sigma with
                           | None -> acc
                           | Some centry ->
                               let rho_c = A.aenv_add x v centry.A.rho in
                               walk cfg h kidx_c centry.A.kont cont rho_c acc)
                       | _ -> acc))
                 [] kont))

  (** {1 The paper-faithful walk (def:absmacro / def:abstransfer)}

      The per-path walk above is a strict {e refinement} of the paper's abstract
      macro transfer. This variant realizes [F_⟦T⟧] literally by restoring its two
      coarsening devices, so that thm:decomposition applies and the fixpoint must
      equal the base analyzer's own per-label network: {b join-then-step}
      (def:absmacro's chain elements [σ_i]), where a [Match]'s per-tuple bindings
      join into one environment per branch; and {b the off-chain leak [F^⋉]}, where
      every state the chain traverses is emitted as a successor through
      [partitions_of] — which is also what lets the walk serve the paper-exact
      instance ([~exact:true]), that routing applying the instance's per-ℓt splits
      and env pins at every chain index, each split continuing as its own chain.
      Function bodies are trees, so paths of one application meet only at a Match
      branch target and the branch join is already the full per-index join. *)

  let rec fwalk ~(leak : bool) (cfg : config) (h : A.handle) (k : A.kidx)
      (kont : A.kont) (phi : Partition.t) (cmd : S.cmd) (rho : A.aenv)
      (acc : A.succ list) : A.succ list =
    (* [cmd] is the command at [lab phi], resolved once by the caller: [route]
       already dispatches on it and every split of one arrival shares the label *)
    let actx () = A.actx_of phi k in
    match cmd with
    | S.Return _ ->
        (* cut: the arrival emission tabulated it; its own pop resumes *)
        acc
    | S.Let (x, e, cont) -> (
        match A.abs_exp ~actx:(actx ()) rho e with
        | None -> acc
        | Some v -> route ~leak cfg h k kont cont (A.aenv_add x v rho) acc)
    | S.LetCall (x, f, args, cont) -> (
        match A.abs_exps ~actx:(actx ()) rho args with
        | None -> acc
        | Some arg_vals ->
            if is_aux cfg f then
              let v_opt =
                match cfg.aux_impl with Fold denot -> denot f arg_vals
              in
              match v_opt with
              | None -> acc
              | Some v -> route ~leak cfg h k kont cont (A.aenv_add x v rho) acc
            else
              (* the frame entry was emitted by the arrival routing; inline
                 the base's AbsLetCall for THIS (possibly split) frame *)
              match A.find_fun h f with
              | None -> acc
              | Some def ->
                  if List.length def.S.params <> List.length arg_vals then acc
                  else
                    let callee_rho =
                      List.fold_left2
                        (fun e p v -> A.aenv_add p v e)
                        A.aenv_empty def.S.params arg_vals
                    in
                    let kidx' = A.push h phi def k in
                    let callee_kont =
                      [ A.KPart { A.pphi = phi; A.pkont = k } ]
                    in
                    List.fold_left
                      (fun acc (phi', rho') ->
                        ((phi', kidx'), rho', callee_kont) :: acc)
                      acc
                      (A.partitions_of h def.S.entry callee_rho))
    | S.Match (e, branches) -> (
        match A.abs_exp ~actx:(actx ()) rho e with
        | None -> acc
        | Some scrut ->
            List.fold_left
              (fun acc (S.PTag (tag, vars), cont) ->
                let arity = List.length vars in
                if D.has_tag tag scrut then
                  match D.fields tag arity scrut with
                  | Some tuples ->
                      let joined =
                        List.fold_left
                          (fun acc_rho tuple ->
                            if List.length tuple = arity then
                              let rho' =
                                List.fold_left2
                                  (fun e y v -> A.aenv_add y (D.gc v) e)
                                  rho vars tuple
                              in
                              match acc_rho with
                              | None -> Some rho'
                              | Some r -> Some (A.aenv_join r rho')
                            else acc_rho)
                          None tuples
                      in
                      (match joined with
                      | None -> acc
                      | Some rho' -> route ~leak cfg h k kont cont rho' acc)
                  | None -> acc
                else acc)
              acc branches)

  (* Arrival at [cont]: emit the successor entries exactly as the base's
     per-label step would ([partitions_of] applies the paper-exact instance's
     split and pin), then continue the chain into each split, stopping at
     [Return] cuts and inlining through everything else. *)
  and route ~(leak : bool) (cfg : config) (h : A.handle) (k : A.kidx)
      (kont : A.kont) (cont : Label.t) (rho : A.aenv) (acc : A.succ list) :
      A.succ list =
    (* without the leak only the functionally required cuts are tabulated —
       Return entries (popped to resume) and caller frames (read by AbsReturn);
       interiors are traversed without being recorded *)
    let cmd = S.cmd_at h.A.prog cont in
    let is_cut =
      (* the continuation is never a head, so [role_of_cmd] suffices *)
      match role_of_cmd (is_aux cfg) cmd with
      | Return_cut | Frame_cut -> true
      | Head | Aux_call | Interior -> false
    in
    List.fold_left
      (fun acc (phi', rho') ->
        let acc =
          if leak || is_cut then ((phi', k), rho', kont) :: acc else acc
        in
        match cmd with
        | S.Return _ -> acc
        | _ -> fwalk ~leak cfg h k kont phi' cmd rho' acc)
      acc
      (A.partitions_of h cont rho)

  (** The paper-faithful step: [heads] are the chain starts, the cuts whose pops
      run a whole [F_⟦T⟧] application ([main] and the callee entries); every
      other tabulated [Let]/[Match] key is a leaked interior, passive like a
      frame. *)
  let step_faithful_gen ~(leak : bool) (cfg : config) (heads : Label.Set.t)
      (h : A.handle) (sigma : A.state) ((phi, k) : A.Key.t) (rho : A.aenv)
      (kont : A.kont) : A.succ list =
    let l = Partition.lab phi in
    let cmd = S.cmd_at h.A.prog l in
    (* the single classifier, sharing [cmd] with the payload match below *)
    let role = if Label.Set.mem l heads then Head else role_of_cmd (is_aux cfg) cmd in
    match role, cmd with
    | Head, _ ->
        (* heads are [Let]/[Match] labels; run the whole chain *)
        List.rev (fwalk ~leak cfg h k kont phi cmd rho [])
    | (Interior | Frame_cut | Aux_call), _ ->
        incr last_passive_pops;
        []
    | Return_cut, S.Return a -> (
        match A.abs_exp ~actx:(A.actx_of phi k) rho a with
        | None -> []
        | Some v ->
            List.rev
              (List.fold_left
                 (fun acc (e : A.kelem) ->
                   match e with
                   | A.KEmpty -> acc
                   | A.KPart caller -> (
                       let phi_c = caller.A.pphi and kidx_c = caller.A.pkont in
                       match S.cmd_at h.A.prog (Partition.lab phi_c) with
                       | S.LetCall (x, _f, _args, cont) -> (
                           match A.Table.find_opt (phi_c, kidx_c) sigma with
                           | None -> acc
                           | Some centry ->
                               let rho_c = A.aenv_add x v centry.A.rho in
                               route ~leak cfg h kidx_c centry.A.kont cont
                                 rho_c acc)
                       | _ -> acc))
                 [] kont))
    | Return_cut, _ -> []

  (** The full paper transfer (join-then-step + the off-chain leak):
      thm:decomposition's equality with the base's per-label network, interiors
      included. *)
  let step_faithful (cfg : config) (heads : Label.Set.t) = step_faithful_gen ~leak:true cfg heads

  (** The specialized (cut-limited) transfer with joins: the per-index joins
      without the off-chain leak, so interiors are traversed but never
      tabulated. The joins make interior elimination an exact substitution, so
      the fixpoint equals the base's per-label network restricted to the cut
      points unconditionally — where the per-path walk only refines it. *)
  let step_fminus (cfg : config) (heads : Label.Set.t) = step_faithful_gen ~leak:false cfg heads

end

(** {1 Default instance: the tree-grammar domain (the base analyzer's image)} *)

include MakeA (Domain_rtg) (S_abstract)

(** The certificate-gated configuration for the default domain. *)
let config () : config =
  { aux_names = certified_aux_names (); aux_impl = Fold Domain_rtg.aux_denot }

type analysis = { table : S_abstract.state; result : Domain_rtg.t }

(** (worklist pops, passive frame pops, populated table entries) of the most
    recent run; productive pops = pops - passive. *)
let last_stats : (int * int * int) ref = ref (0, 0, 0)

let run_rtg (cfg : config) (arg : Domain_rtg.t) (p : T_encoding.program) :
    analysis =
  last_passive_pops := 0;
  let a = S_abstract.analyze_t_with ~step:(step cfg) ~arg p in
  last_stats :=
    ( !S_abstract.last_solve_steps,
      !last_passive_pops,
      S_abstract.table_size a.S_abstract.table );
  { table = a.S_abstract.table; result = a.S_abstract.result }

(** Analyze a T program with the specialized image of the base analyzer over
    {!Domain_rtg}, auxiliary calls discharged by the auxiliary denotations; only
    the step is the residual, everything around it being
    {!S_abstract.analyze_t}'s own code. *)
let analyze_t ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    (p : T_encoding.program) : analysis =
  run_rtg (config ()) arg p

(** No auxiliary summarization: with an empty auxiliary family every call site
    (including [lookup]/[fundef]/[extend]) is an ordinary cut and the auxiliaries
    are analyzed through the shared table as in the base, while the straight-line
    glue between cuts is still composed. Isolates what macro steps alone buy. *)
let analyze_t_analyzed ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    (p : T_encoding.program) : analysis =
  let cfg =
    { aux_names = []; aux_impl = Fold (fun _ _ -> None) (* never consulted *) }
  in
  run_rtg cfg arg p

(** The chain-start labels of the two networks (see {!MakeA.step_faithful}). *)
let heads_fold () : Label.Set.t =
  let aux = certified_aux_names () in
  heads_of (fun f -> List.exists (String.equal f) aux) Interp_st.program

let heads_analyzed () : Label.Set.t =
  heads_of (fun _ -> false) Interp_st.program

(** The write-only keys of a paper-faithful network: frames and leaked interiors
    yield no successors when popped, so the solver may skip re-enqueueing them on
    growth ([?passive] of {!S_abstract.solve}). A pure scheduling optimization —
    the table and every active step are unchanged. *)
let faithful_passive (heads : Label.Set.t) : Partition.t * 'k -> bool =
 fun (phi, _) ->
  (* passivity is aux-independent (both LetCall roles are passive frames) *)
  match site_role (fun _ -> false) heads Interp_st.program (Partition.lab phi) with
  | Head | Return_cut -> false
  | Frame_cut | Aux_call | Interior -> true

let run_rtg_step
    ?(passive : (S_abstract.Key.t -> bool) option)
    ?(exact = false)
    (stepf : S_abstract.handle -> S_abstract.state -> S_abstract.Key.t ->
             S_abstract.aenv -> S_abstract.kont -> S_abstract.succ list)
    (arg : Domain_rtg.t) (p : T_encoding.program) : analysis =
  last_passive_pops := 0;
  let a = S_abstract.analyze_t_with ~step:stepf ?passive ~exact ~arg p in
  last_stats :=
    ( !S_abstract.last_solve_steps,
      !last_passive_pops,
      S_abstract.table_size a.S_abstract.table );
  { table = a.S_abstract.table; result = a.S_abstract.result }

(** The paper-faithful transfer (def:absmacro literally; see
    {!MakeA.step_faithful}). With the auxiliary denotations it targets
    thm:decomposition's equality with the hand-written macro engine; with the
    auxiliaries analyzed, equality with the base analyzer. [~exact:true] runs the
    paper-exact instance (exercised by tests/test_exact_disc.ml). *)
let analyze_t_faithful ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    ?(exact = false) (p : T_encoding.program) : analysis =
  let heads = heads_fold () in
  run_rtg_step
    ~passive:(faithful_passive heads)
    ~exact
    (step_faithful (config ()) heads)
    arg p

let analyze_t_faithful_analyzed ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    ?(exact = false) (p : T_encoding.program) : analysis =
  let cfg = { aux_names = []; aux_impl = Fold (fun _ _ -> None) } in
  let heads = heads_analyzed () in
  run_rtg_step
    ~passive:(faithful_passive heads)
    ~exact
    (step_faithful cfg heads)
    arg p

(** The specialized (cut-limited) transfer with joins ({!MakeA.step_fminus}):
    the paper's per-index precision at the cut points, no interior bookkeeping.
    [~exact:true] runs the paper-exact instance through the same [fwalk]
    routing. *)
let analyze_t_fminus ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    ?(exact = false) (p : T_encoding.program) : analysis =
  let heads = heads_fold () in
  run_rtg_step
    ~passive:(faithful_passive heads)
    ~exact
    (step_fminus (config ()) heads)
    arg p

let analyze_t_fminus_analyzed ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    ?(exact = false) (p : T_encoding.program) : analysis =
  let cfg = { aux_names = []; aux_impl = Fold (fun _ _ -> None) } in
  let heads = heads_analyzed () in
  run_rtg_step
    ~passive:(faithful_passive heads)
    ~exact
    (step_fminus cfg heads)
    arg p

(** {1 The disambiguated instance (the disambiguated value domain image)}

    The specialized step instantiated at {!Domain_dis}: the disambiguated-domain
    driver with the specialized step swapped in, so that the mechanical image can
    be compared to the hand-written calculated-machine analyzer at one domain. *)

type dis_analysis = {
  result : Domain_intf.aint;
  pops : int;
  passive : int;
  cells : int;
}

let run_dis (arg : Domain_rtg.t) (p : T_encoding.program) : dis_analysis =
  let module Dd = Domain_dis.Make (struct
    let prog = p
  end) in
  let module Ad = S_abstract.Make (Dd) in
  let module C = MakeA (Dd) (Ad) in
  let cfg =
    { C.aux_names = certified_aux_names (); C.aux_impl = C.Fold Dd.aux_denot }
  in
  C.last_passive_pops := 0;
  let h = Ad.handle_for_interp () in
  let rho0 =
    Ad.initial_env (Dd.prog_value ()) (Dd.of_aint (Domain_rtg.root_int arg))
  in
  let phi0 = Ad.partition_of h h.Ad.prog.S.main rho0 in
  let init =
    Ad.Table.add (phi0, Ad.KBullet)
      { Ad.rho = rho0; Ad.kont = Ad.kont_halt }
      Ad.state_empty
  in
  let table = Ad.solve ~step:(C.step cfg) h init in
  {
    result = Dd.root_int (Ad.read_result h table);
    pops = !Ad.last_solve_steps;
    passive = !C.last_passive_pops;
    cells = Ad.table_size table;
  }

let analyze_t_dis ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    (p : T_encoding.program) : dis_analysis =
  run_dis arg p

(** The specialized analyzer with both precision retargetings, at the designated
    paper instance: {!MakeA.step_fminus} over {!Domain_dis}'s program-derived
    keyed grammar, auxiliaries discharged by [Dd.aux_denot], and — under
    [~exact:true] — the paper-exact pins built per program. Pairs with
    {!analyze_t_fminus_analyzed} [~exact:true], the same machinery with neither
    retargeting. *)
let analyze_t_dis_fminus ?(arg : Domain_rtg.t = Domain_rtg.int_lit 0)
    ?(exact = false) (p : T_encoding.program) : dis_analysis =
  let module Dd = Domain_dis.Make (struct
    let prog = p
  end) in
  let module Ad = S_abstract.Make (Dd) in
  let module C = MakeA (Dd) (Ad) in
  let cfg =
    { C.aux_names = certified_aux_names (); C.aux_impl = C.Fold Dd.aux_denot }
  in
  let heads = heads_fold () in
  C.last_passive_pops := 0;
  let h0 = Ad.handle_for_interp () in
  let h =
    if not exact then h0
    else
      let pins =
        List.fold_left
          (fun acc (l, e) ->
            let pv = Dd.abstract_value (T_encoding.enc_expr e) in
            Label.Map.update l
              (function None -> Some pv | Some old -> Some (Dd.join old pv))
              acc)
          Label.Map.empty
          (T_encoding.labeled_sub_exprs p)
      in
      { h0 with Ad.exact_pins = Some pins }
  in
  let rho0 =
    Ad.initial_env (Dd.prog_value ()) (Dd.of_aint (Domain_rtg.root_int arg))
  in
  let phi0 = Ad.partition_of h h.Ad.prog.S.main rho0 in
  let init =
    Ad.Table.add (phi0, Ad.KBullet)
      { Ad.rho = rho0; Ad.kont = Ad.kont_halt }
      Ad.state_empty
  in
  let table =
    Ad.solve
      ~step:(C.step_fminus cfg heads)
      ~passive:(faithful_passive heads)
      h init
  in
  {
    result = Dd.root_int (Ad.read_result h table);
    pops = !Ad.last_solve_steps;
    passive = !C.last_passive_pops;
    cells = Ad.table_size table;
  }
