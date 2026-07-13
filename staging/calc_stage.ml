(* The generator for the STORED specialized analyzer: emits it as code.

   The subject is Calc_pe's specialized transfer (lib/calc_pe.ml) — the
   composition of the base abstract interpreter's micro-transfers along the
   segments its own table reads force. This generator partially evaluates that
   transfer w.r.t. the interpreter text I_S^T and emits the residual as plain
   OCaml: brackets against the CONCRETE modules (Retargeting.Domain_rtg /
   Retargeting.S_abstract), a fixed transparent prefix rewrite lifting the
   emitted text to a functor over (D, A), a printf'd glue dispatch, and a
   deterministic provenance digest.

   What is resolved statically (per segment): the command chain and its
   shapes (no cmd_at at analysis time), the eval-dispatch branch tags,
   arities, and binder names, the auxiliary callee names and their
   pusĥ-classification (eval-call → •; aux-from-eval-body → the T-context
   stash), the non-aux callee's entry and formals, the caller-site resume
   dispatch (an if-chain over the static non-aux LetCall sites, emitted
   ONCE), and the observed-return expressions. What stays dynamic: domain
   values, the string-keyed abstract environments, partitions_of /
   partition_of / actx_of / the table — the base runtime the generated
   transfer plugs into through A.solve ~step (via A.analyze_t_with), so the
   fixpoint discipline is inherited, not re-derived.

   The auxiliary operator is a PARAMETER of the generated transfer
   ([aux : A.handle -> string -> A.kidx -> D.t list -> D.t option]), so ONE
   stored artifact serves both forms: the auxiliary denotations
   (Domain_rtg.aux_denot / Domain_dis.Make.aux_denot) and the auxiliary
   summary (the auxiliary bodies analyzed through the shared table). The
   generator refuses to run without the Role_pe certificate — the segment
   composition is meaningless without the auxiliary macro-steps.

   Emitted to lib_gen/generated_calc.ml; scripts/run-gen-calc.sh. *)

open Codelib
module S = Retargeting.S_syntax
module I = Retargeting.Interp_st
module A = Retargeting.S_abstract
module Lab = Retargeting.Label

(* ---------------------------------------------------------------------- *)
(* Generation-time statics.                                                *)
(* ---------------------------------------------------------------------- *)

let iprog : S.program = I.program
let h0 : A.handle = A.handle_for_interp ()
let eval_entry : Lab.t = h0.A.eval_entry
let eval_body : Lab.Set.t = h0.A.eval_body
let main_l : Lab.t = iprog.S.main

let find_fun (f : string) : S.fundef =
  match List.find_opt (fun d -> String.equal d.S.name f) iprog.S.funs with
  | Some d -> d
  | None -> failwith ("calc_stage: interpreter lacks " ^ f)

(* The certified auxiliary family — REQUIRED: the specialized transfer folds every
   auxiliary call into a summary application, so without the certificate there is
   nothing sound to emit, and generation refuses rather than guessing. *)
let aux_names : string list =
  match Retargeting.Role_pe.certify_interp_st () with
  | Error msgs ->
      failwith
        ("calc_stage: auxiliary family not certified: "
        ^ String.concat "; " msgs)
  | Ok cert ->
      List.map
        (fun (a : Retargeting.Role_pe.aux_summary) -> a.Retargeting.Role_pe.name)
        cert.Retargeting.Role_pe.aux

let is_aux (f : string) : bool = List.exists (String.equal f) aux_names

(* Reachable labels from an entry through continuation edges. *)
let body_labels (entry : Lab.t) : Lab.t list =
  let seen = Hashtbl.create 64 in
  let acc = ref [] in
  let rec go l =
    if not (Hashtbl.mem seen l) then begin
      Hashtbl.add seen l ();
      acc := l :: !acc;
      match S.cmd_at iprog l with
      | S.Return _ -> ()
      | S.Let (_, _, k) -> go k
      | S.LetCall (_, _, _, k) -> go k
      | S.Match (_, bs) -> List.iter (fun (_, k) -> go k) bs
    end
  in
  go entry;
  List.sort compare !acc

(* The specialized transfer's static label classification — derived from the same
   cut criterion as lib/calc_pe.ml (a table-free successor is inlined; frames,
   callee entries, and returns are cuts). Only eval's body and main matter:
   the auxiliary bodies are never tabulated (their calls fold to summaries). *)
let network_labels : Lab.t list = body_labels eval_entry @ body_labels main_l

(* observed returns: every Return command of the network (eval's L_ret plus
   main's terminal return), each with its returned expression *)
let ret_sites : (Lab.t * S.exp) list =
  List.filter_map
    (fun l ->
      match S.cmd_at iprog l with S.Return a -> Some (l, a) | _ -> None)
    network_labels

(* caller frames: the non-auxiliary LetCall sites (the paper's L_call plus the
   root call), each with its bound variable and continuation *)
let frame_sites : (Lab.t * (string * Lab.t)) list =
  List.filter_map
    (fun l ->
      match S.cmd_at iprog l with
      | S.LetCall (x, f, _, cont) when not (is_aux f) -> Some (l, (x, cont))
      | _ -> None)
    network_labels

(* The analyzed-auxiliary transfer set: no summaries at all, so every
   call site — auxiliary ones included — is an ordinary cut, and the network
   spans every function body. Mirrors lib/calc_pe.ml's [analyze_t_analyzed]
   (the empty auxiliary family). *)
let network_labels_a : Lab.t list =
  List.concat_map (fun (d : S.fundef) -> body_labels d.S.entry) iprog.S.funs
  @ body_labels main_l

let ret_sites_a : (Lab.t * S.exp) list =
  List.filter_map
    (fun l ->
      match S.cmd_at iprog l with S.Return a -> Some (l, a) | _ -> None)
    network_labels_a

let frame_sites_a : (Lab.t * (string * Lab.t)) list =
  List.filter_map
    (fun l ->
      match S.cmd_at iprog l with
      | S.LetCall (x, _, _, cont) -> Some (l, (x, cont))
      | _ -> None)
    network_labels_a

(* the analyzed network's segment heads: main plus every function entry
   (callee entries are cuts for eval AND the auxiliaries) *)
let entry_heads_a : Lab.t list =
  List.map (fun (d : S.fundef) -> d.S.entry) iprog.S.funs

(* ---------------------------------------------------------------------- *)
(* Lifting static data across the stage.                                   *)
(* ---------------------------------------------------------------------- *)

let code_of_string_list (xs : string list) : string list code =
  List.fold_right (fun (x : string) acc -> .< x :: .~acc >.) xs .< [] >.

(* ---------------------------------------------------------------------- *)
(* Expression compilation: the base abs_exp with the tree folded away.     *)
(* Variable reads become aenv_find with a literal name; the allocation      *)
(* context is the spliced-in per-command actx.                              *)
(* ---------------------------------------------------------------------- *)

type ctx = {
  rho : Retargeting.S_abstract.aenv code;
  actx : Lab.t list code;
}

let rec gen_exp (cx : ctx) (e : S.exp) : Retargeting.Domain_rtg.t option code =
  match e with
  | S.EInt n -> .< Some (Retargeting.Domain_rtg.int_lit n) >.
  | S.EVar x -> .< Some (Retargeting.S_abstract.aenv_find .~(cx.rho) x) >.
  | S.EPrim (o, es) ->
      gen_operands cx es (fun vs -> .< Retargeting.Domain_rtg.prim o .~vs >.)
  | S.ETag (site, t, es) ->
      gen_operands cx es (fun vs ->
          .<
            (let st =
               if .~(cx.actx) = [] then Retargeting.Domain_rtg.Internal site
               else Retargeting.Domain_rtg.InternalT (site, .~(cx.actx))
             in
             Some (Retargeting.Domain_rtg.tag st t .~vs))
          >.)

and gen_operands (cx : ctx) (es : S.exp list)
    (k :
      Retargeting.Domain_rtg.t list code ->
      Retargeting.Domain_rtg.t option code) : Retargeting.Domain_rtg.t option code
    =
  let rec go es (vs_rev : Retargeting.Domain_rtg.t code list) =
    match es with
    | [] ->
        let vs =
          List.fold_left (fun acc v -> .< .~v :: .~acc >.) .< [] >. vs_rev
        in
        k vs
    | e :: rest ->
        .<
          match .~(gen_exp cx e) with
          | None -> None
          | Some v -> .~(go rest (.< v >. :: vs_rev))
        >.
  in
  go es []

(* like [gen_operands] but in successor-list position: the continuation builds
   a [succ list] and an uninterpretable operand short-circuits to [none] (the
   untouched accumulator), mirroring the in-process walk's [None -> acc]. *)
let gen_args (cx : ctx) (es : S.exp list)
    ~(none : Retargeting.S_abstract.succ list code)
    (k :
      Retargeting.Domain_rtg.t list code ->
      Retargeting.S_abstract.succ list code) :
    Retargeting.S_abstract.succ list code =
  let rec go es (vs_rev : Retargeting.Domain_rtg.t code list) =
    match es with
    | [] ->
        let vs =
          List.fold_left (fun acc v -> .< .~v :: .~acc >.) .< [] >. vs_rev
        in
        k vs
    | e :: rest ->
        .<
          match .~(gen_exp cx e) with
          | None -> .~none
          | Some v -> .~(go rest (.< v >. :: vs_rev))
        >.
  in
  go es []

(* ---------------------------------------------------------------------- *)
(* Segment compilation: the residual of Calc_pe.walk from a label.          *)
(* Mirrors lib/calc_pe.ml [walk] arm for arm — same operations, same order,  *)
(* same successor construction (acc-prepending; the glue List.rev's) — with  *)
(* every static resolved: shapes, tags, arities, binder names, the pusĥ      *)
(* classification, the callee entry/formals.                                 *)
(* ---------------------------------------------------------------------- *)

type wctx = {
  ax : string -> bool;
      (** generation-time: is this callee summarized (folded via the [aux]
          parameter)? [fun _ -> false] generates the analyzed-aux arm. *)
  aux :
    (Retargeting.S_abstract.handle ->
    string ->
    Retargeting.S_abstract.kidx ->
    Retargeting.Domain_rtg.t list ->
    Retargeting.Domain_rtg.t option)
    code;
  h : Retargeting.S_abstract.handle code;
  k : Retargeting.S_abstract.kidx code;
  kont : Retargeting.S_abstract.kont code;
}

let rec gen_walk (w : wctx) (l : Lab.t)
    (rho : Retargeting.S_abstract.aenv code)
    (acc : Retargeting.S_abstract.succ list code) :
    Retargeting.S_abstract.succ list code =
  match S.cmd_at iprog l with
  | S.Return _ ->
      (* cut: tabulate the observed return state *)
      .<
        List.fold_left
          (fun acc (phi', rho') -> ((phi', .~(w.k)), rho', .~(w.kont)) :: acc)
          .~acc
          (Retargeting.S_abstract.partitions_of .~(w.h) l .~rho)
      >.
  | S.Let (x, e, cont) ->
      (* [AbsLetExp], inlined *)
      .<
        (let actx =
           Retargeting.S_abstract.actx_of
             (Retargeting.S_abstract.partition_of .~(w.h) l .~rho)
             .~(w.k)
         in
         match .~(gen_exp { rho; actx = .< actx >. } e) with
         | None -> .~acc
         | Some v ->
             let rho = Retargeting.S_abstract.aenv_add x v .~rho in
             .~(gen_walk w cont .< rho >. acc))
      >.
  | S.LetCall (x, f, args, cont) ->
      if w.ax f then
        (* the auxiliary macro-step, folded to the summary parameter; its
           continuation index is the statically-classified pusĥ (an aux call
           from eval's body stashes the T-context; main's glue passes κ̂) *)
        let in_eval_body = Lab.Set.mem l eval_body in
        .<
          (let actx =
             Retargeting.S_abstract.actx_of
               (Retargeting.S_abstract.partition_of .~(w.h) l .~rho)
               .~(w.k)
           in
           .~(gen_args { rho; actx = .< actx >. } args ~none:acc (fun vs ->
                  .<
                    (let kidx' =
                       .~(if in_eval_body then
                            .<
                              Retargeting.S_abstract.KTLabs
                                (Retargeting.S_abstract.partition_of .~(w.h) l
                                   .~rho)
                                  .Retargeting.Partition.t_label
                            >.
                          else w.k)
                     in
                     match .~(w.aux) .~(w.h) f kidx' .~vs with
                     | None -> .~acc
                     | Some v ->
                         let rho = Retargeting.S_abstract.aenv_add x v .~rho in
                         .~(gen_walk w cont .< rho >. acc))
                  >.)))
        >.
      else begin
        (* cut: [AbsLetCall] — tabulate the caller frame and the callee entry.
           The callee is [eval] (statically known), so the retargeted pusĥ is
           the constant •; the frame part carries its real κ̂. *)
        let def = find_fun f in
        if List.length def.S.params <> List.length args then acc
        else
          let params = code_of_string_list def.S.params in
          let entry = def.S.entry in
          let is_eval_call = Lab.equal entry eval_entry in
          let in_eval_body = Lab.Set.mem l eval_body in
          .<
            (let actx =
               Retargeting.S_abstract.actx_of
                 (Retargeting.S_abstract.partition_of .~(w.h) l .~rho)
                 .~(w.k)
             in
             .~(gen_args { rho; actx = .< actx >. } args ~none:acc (fun vs ->
                    .<
                      (let phi_l =
                         Retargeting.S_abstract.partition_of .~(w.h) l .~rho
                       in
                       let acc = ((phi_l, .~(w.k)), .~rho, .~(w.kont)) :: .~acc in
                       let callee_rho =
                         List.fold_left2
                           (fun e p v -> Retargeting.S_abstract.aenv_add p v e)
                           Retargeting.S_abstract.aenv_empty .~params .~vs
                       in
                       let kidx' =
                         .~(if is_eval_call then
                              .< Retargeting.S_abstract.KBullet >.
                            else if in_eval_body then
                              .<
                                Retargeting.S_abstract.KTLabs
                                  phi_l.Retargeting.Partition.t_label
                              >.
                            else w.k)
                       in
                       let callee_kont =
                         [
                           Retargeting.S_abstract.KPart
                             {
                               Retargeting.S_abstract.pphi = phi_l;
                               Retargeting.S_abstract.pkont = .~(w.k);
                             };
                         ]
                       in
                       List.fold_left
                         (fun acc (phi', rho') ->
                           ((phi', kidx'), rho', callee_kont) :: acc)
                         acc
                         (Retargeting.S_abstract.partitions_of .~(w.h) entry
                            callee_rho))
                    >.)))
          >.
      end
  | S.Match (e, branches) ->
      (* [AbsMatch], inlined: every feasible branch continues the walk; the
         branches thread the accumulator left to right, as the base fold does *)
      .<
        (let actx =
           Retargeting.S_abstract.actx_of
             (Retargeting.S_abstract.partition_of .~(w.h) l .~rho)
             .~(w.k)
         in
         match .~(gen_exp { rho; actx = .< actx >. } e) with
         | None -> .~acc
         | Some scrut ->
             .~(List.fold_left
                  (fun acc_c (S.PTag (tag, vars), cont) ->
                    let arity = List.length vars in
                    let vars_c = code_of_string_list vars in
                    .<
                      (let acc = .~acc_c in
                       if Retargeting.Domain_rtg.has_tag tag scrut then
                         match Retargeting.Domain_rtg.fields tag arity scrut with
                         | Some tuples ->
                             List.fold_left
                               (fun acc tuple ->
                                 if List.length tuple = arity then begin
                                   let rho =
                                     List.fold_left2
                                       (fun e y v ->
                                         Retargeting.S_abstract.aenv_add y
                                           (Retargeting.Domain_rtg.gc v) e)
                                       .~rho .~vars_c tuple
                                   in
                                   .~(gen_walk w cont .< rho >. .< acc >.)
                                 end
                                 else acc)
                               acc tuples
                         | None -> acc
                       else acc)
                    >.)
                  acc branches))
      >.

(* ---------------------------------------------------------------------- *)
(* The three residual leaves: the two segment heads and the return arm.     *)
(* (The caller-site resume dispatch is emitted ONCE, inside the return      *)
(* arm — the readable-residual discipline.)                                 *)
(* ---------------------------------------------------------------------- *)

(* a segment head (the initial main state / the eval-entry dispatch):
   aux -> h -> k -> kont -> rho -> succs (unreversed; the glue List.rev's) *)
let gen_head ~(ax : string -> bool) (l : Lab.t) : 'a code =
  .<
    fun aux h k kont rho ->
      .~(gen_walk
           { ax; aux = .< aux >.; h = .< h >.; k = .< k >.; kont = .< kont >. }
           l .< rho >. .< [] >.)
  >.

(* the return arm: AbsReturn's precise caller lookup fused with the resume
   segment of the caller's site. The observed-return expression dispatches on
   the popped label (all Return sites of the network); the resume dispatches
   on the caller's site label — both static if-chains. *)
let gen_return_all ~(ax : string -> bool)
    ~(rets : (Lab.t * S.exp) list) ~(frames : (Lab.t * (string * Lab.t)) list)
    : 'a code =
  .<
    fun aux h sigma phi k rho kont ->
      let l = Retargeting.Partition.lab phi in
      let actx = Retargeting.S_abstract.actx_of phi k in
      let v_opt =
        .~(List.fold_right
             (fun (lr, a) rest ->
               .<
                 if l = lr then
                   .~(gen_exp { rho = .< rho >.; actx = .< actx >. } a)
                 else .~rest
               >.)
             rets .< None >.)
      in
      match v_opt with
      | None -> []
      | Some v ->
          List.rev
            (List.fold_left
               (fun acc e ->
                 match e with
                 | Retargeting.S_abstract.KEmpty -> acc
                 | Retargeting.S_abstract.KPart caller -> (
                     let phi_c = caller.Retargeting.S_abstract.pphi in
                     let kidx_c = caller.Retargeting.S_abstract.pkont in
                     match
                       Retargeting.S_abstract.Table.find_opt (phi_c, kidx_c)
                         sigma
                     with
                     | None -> acc
                     | Some centry ->
                         let lc = Retargeting.Partition.lab phi_c in
                         let ckont = centry.Retargeting.S_abstract.kont in
                         .~(List.fold_right
                              (fun (site, ((x : string), cont)) rest ->
                                .<
                                  if lc = site then begin
                                    let rho =
                                      Retargeting.S_abstract.aenv_add x v
                                        centry.Retargeting.S_abstract.rho
                                    in
                                    .~(gen_walk
                                         {
                                           ax;
                                           aux = .< aux >.;
                                           h = .< h >.;
                                           k = .< kidx_c >.;
                                           kont = .< ckont >.;
                                         }
                                         cont .< rho >. .< acc >.)
                                  end
                                  else .~rest
                                >.)
                              frames .< acc >.)))
               [] kont)
  >.

(* ---------------------------------------------------------------------- *)
(* The paper-faithful / specialized-transfer walk (calc_pe fwalk/route):    *)
(* Match branches, arrivals routed through partitions_of with the emission  *)
(* gated by [leak || is_cut] (is_cut static per site; leak a runtime bool,  *)
(* exactly the in-process ~leak parameter). The popped key's partition phi  *)
(* is threaded (actx_of phi k — no re-decode), mirroring fwalk op for op.   *)
(* ---------------------------------------------------------------------- *)

type fwctx = {
  fax : string -> bool;
  faux :
    (Retargeting.S_abstract.handle ->
    string ->
    Retargeting.S_abstract.kidx ->
    Retargeting.Domain_rtg.t list ->
    Retargeting.Domain_rtg.t option)
    code;
  fleak : bool code;
  fh : Retargeting.S_abstract.handle code;
  fk : Retargeting.S_abstract.kidx code;
  fkont : Retargeting.S_abstract.kont code;
}

let rec gen_fwalk (w : fwctx) (l : Lab.t)
    (phi : Retargeting.Partition.t code)
    (rho : Retargeting.S_abstract.aenv code)
    (acc : Retargeting.S_abstract.succ list code) :
    Retargeting.S_abstract.succ list code =
  match S.cmd_at iprog l with
  | S.Return _ ->
      (* cut: the arrival emission tabulated it; its own pop resumes *)
      acc
  | S.Let (x, e, cont) ->
      .<
        (let actx =
           Retargeting.S_abstract.actx_of .~phi .~(w.fk)
         in
         match .~(gen_exp { rho; actx = .< actx >. } e) with
         | None -> .~acc
         | Some v ->
             let rho = Retargeting.S_abstract.aenv_add x v .~rho in
             .~(gen_froute w cont .< rho >. acc))
      >.
  | S.LetCall (x, f, args, cont) ->
      if w.fax f then
        let in_eval_body = Lab.Set.mem l eval_body in
        .<
          (let actx =
             Retargeting.S_abstract.actx_of .~phi .~(w.fk)
           in
           .~(gen_args { rho; actx = .< actx >. } args ~none:acc (fun vs ->
                  .<
                    (let kidx' =
                       .~(if in_eval_body then
                            .<
                              Retargeting.S_abstract.KTLabs
                                (.~phi).Retargeting.Partition.t_label
                            >.
                          else w.fk)
                     in
                     match .~(w.faux) .~(w.fh) f kidx' .~vs with
                     | None -> .~acc
                     | Some v ->
                         let rho = Retargeting.S_abstract.aenv_add x v .~rho in
                         .~(gen_froute w cont .< rho >. acc))
                  >.)))
        >.
      else begin
        (* the frame entry was emitted by the arrival routing; inline the
           base's AbsLetCall for THIS frame *)
        let def = find_fun f in
        if List.length def.S.params <> List.length args then acc
        else
          let params = code_of_string_list def.S.params in
          let entry = def.S.entry in
          let is_eval_call = Lab.equal entry eval_entry in
          let in_eval_body = Lab.Set.mem l eval_body in
          .<
            (let actx =
               Retargeting.S_abstract.actx_of .~phi .~(w.fk)
             in
             .~(gen_args { rho; actx = .< actx >. } args ~none:acc (fun vs ->
                    .<
                      (let callee_rho =
                         List.fold_left2
                           (fun e p v -> Retargeting.S_abstract.aenv_add p v e)
                           Retargeting.S_abstract.aenv_empty .~params .~vs
                       in
                       let kidx' =
                         .~(if is_eval_call then
                              .< Retargeting.S_abstract.KBullet >.
                            else if in_eval_body then
                              .<
                                Retargeting.S_abstract.KTLabs
                                  (.~phi).Retargeting.Partition.t_label
                              >.
                            else w.fk)
                       in
                       let callee_kont =
                         [
                           Retargeting.S_abstract.KPart
                             {
                               Retargeting.S_abstract.pphi = .~phi;
                               Retargeting.S_abstract.pkont = .~(w.fk);
                             };
                         ]
                       in
                       List.fold_left
                         (fun acc (phi', rho') ->
                           ((phi', kidx'), rho', callee_kont) :: acc)
                         .~acc
                         (Retargeting.S_abstract.partitions_of .~(w.fh) entry
                            callee_rho))
                    >.)))
          >.
      end
  | S.Match (e, branches) ->
      .<
        (let actx =
           Retargeting.S_abstract.actx_of .~phi .~(w.fk)
         in
         match .~(gen_exp { rho; actx = .< actx >. } e) with
         | None -> .~acc
         | Some scrut ->
             .~(List.fold_left
                  (fun acc_c (S.PTag (tag, vars), cont) ->
                    let arity = List.length vars in
                    let vars_c = code_of_string_list vars in
                    .<
                      (let acc = .~acc_c in
                       if Retargeting.Domain_rtg.has_tag tag scrut then
                         match Retargeting.Domain_rtg.fields tag arity scrut with
                         | Some tuples ->
                             let joined =
                               List.fold_left
                                 (fun acc_rho tuple ->
                                   if List.length tuple = arity then
                                     let rho' =
                                       List.fold_left2
                                         (fun e y v ->
                                           Retargeting.S_abstract.aenv_add y
                                             (Retargeting.Domain_rtg.gc v) e)
                                         .~rho .~vars_c tuple
                                     in
                                     match acc_rho with
                                     | None -> Some rho'
                                     | Some r ->
                                         Some
                                           (Retargeting.S_abstract.aenv_join r
                                              rho')
                                   else acc_rho)
                                 None tuples
                             in
                             (match joined with
                              | None -> acc
                              | Some rho ->
                                  .~(gen_froute w cont .< rho >. .< acc >.))
                         | None -> acc
                       else acc)
                    >.)
                  acc branches))
      >.

(* Arrival at [cont]: emit through partitions_of (gated), continue the chain
   into each split, stopping at Return cuts. *)
and gen_froute (w : fwctx) (cont : Lab.t)
    (rho : Retargeting.S_abstract.aenv code)
    (acc : Retargeting.S_abstract.succ list code) :
    Retargeting.S_abstract.succ list code =
  let cmd = S.cmd_at iprog cont in
  let is_cut =
    match cmd with
    | S.Return _ -> true
    | S.LetCall (_, f, _, _) -> not (w.fax f)
    | S.Let _ | S.Match _ -> false
  in
  let is_ret = match cmd with S.Return _ -> true | _ -> false in
  .<
    List.fold_left
      (fun acc (phi', rho') ->
        let acc =
          .~(if is_cut then
               .< ((phi', .~(w.fk)), rho', .~(w.fkont)) :: acc >.
             else
               .<
                 (if .~(w.fleak) then
                    ((phi', .~(w.fk)), rho', .~(w.fkont)) :: acc
                  else acc)
               >.)
        in
        .~(if is_ret then .< acc >.
           else gen_fwalk w cont .< phi' >. .< rho' >. .< acc >.))
      .~acc
      (Retargeting.S_abstract.partitions_of .~(w.fh) cont .~rho)
  >.

(* a faithful segment head: aux -> leak -> h -> k -> kont -> phi -> rho ->
   succs (unreversed; the glue List.rev's) *)
let gen_fhead ~(ax : string -> bool) (l : Lab.t) : 'a code =
  .<
    fun aux leak h k kont phi rho ->
      .~(gen_fwalk
           {
             fax = ax;
             faux = .< aux >.;
             fleak = .< leak >.;
             fh = .< h >.;
             fk = .< k >.;
             fkont = .< kont >.;
           }
           l .< phi >. .< rho >. .< [] >.)
  >.

(* the faithful return arm: AbsReturn's precise caller lookup, resuming
   through the ROUTED walk (join-then-step; emissions gated by leak) *)
let gen_freturn_all ~(ax : string -> bool)
    ~(rets : (Lab.t * S.exp) list) ~(frames : (Lab.t * (string * Lab.t)) list)
    : 'a code =
  .<
    fun aux leak h sigma phi k rho kont ->
      let l = Retargeting.Partition.lab phi in
      let actx = Retargeting.S_abstract.actx_of phi k in
      let v_opt =
        .~(List.fold_right
             (fun (lr, a) rest ->
               .<
                 if l = lr then
                   .~(gen_exp { rho = .< rho >.; actx = .< actx >. } a)
                 else .~rest
               >.)
             rets .< None >.)
      in
      match v_opt with
      | None -> []
      | Some v ->
          List.rev
            (List.fold_left
               (fun acc e ->
                 match e with
                 | Retargeting.S_abstract.KEmpty -> acc
                 | Retargeting.S_abstract.KPart caller -> (
                     let phi_c = caller.Retargeting.S_abstract.pphi in
                     let kidx_c = caller.Retargeting.S_abstract.pkont in
                     match
                       Retargeting.S_abstract.Table.find_opt (phi_c, kidx_c)
                         sigma
                     with
                     | None -> acc
                     | Some centry ->
                         let lc = Retargeting.Partition.lab phi_c in
                         let ckont = centry.Retargeting.S_abstract.kont in
                         .~(List.fold_right
                              (fun (site, ((x : string), cont)) rest ->
                                .<
                                  if lc = site then begin
                                    let rho =
                                      Retargeting.S_abstract.aenv_add x v
                                        centry.Retargeting.S_abstract.rho
                                    in
                                    .~(gen_froute
                                         {
                                           fax = ax;
                                           faux = .< aux >.;
                                           fleak = .< leak >.;
                                           fh = .< h >.;
                                           fk = .< kidx_c >.;
                                           fkont = .< ckont >.;
                                         }
                                         cont .< rho >. .< acc >.)
                                  end
                                  else .~rest
                                >.)
                              frames .< acc >.)))
               [] kont)
  >.

(* ---------------------------------------------------------------------- *)
(* Emission: emit, functor-rewrite, glue, provenance.                       *)
(* ---------------------------------------------------------------------- *)

let replace_all (sub : string) (rep : string) (s : string) : string =
  let b = Buffer.create (String.length s) in
  let n = String.length sub in
  let i = ref 0 in
  let len = String.length s in
  while !i < len do
    if !i + n <= len && String.sub s !i n = sub then begin
      Buffer.add_string b rep;
      i := !i + n
    end
    else begin
      Buffer.add_char b s.[!i];
      incr i
    end
  done;
  Buffer.contents b

let functor_rewrite (s : string) : string =
  s
  |> replace_all "Retargeting.Domain_rtg." "D."
  |> replace_all "Retargeting.S_abstract." "A."

let string_of_code (code : 'a code) : string =
  let b2 = Buffer.create 256 in
  let fmt = Format.formatter_of_buffer b2 in
  format_code fmt (close_code code);
  Format.pp_print_flush fmt ();
  Buffer.contents b2

(* the step glue and the domain-generic driver, emitted verbatim (already in
   D./A. form). The step mirrors Calc_pe.step's dispatch: segment heads at the
   main / eval-entry labels, the return arm at the observed returns, passive
   frame pops at the caller sites. The driver mirrors Calc_pe.analyze_t:
   A.analyze_t_with with only the step swapped. *)
let glue_text : string =
  let ret_disj =
    String.concat " || " (List.map (fun (l, _) -> Printf.sprintf "l = %d" l) ret_sites)
  in
  let frame_disj =
    String.concat " || "
      (List.map (fun (l, _) -> Printf.sprintf "l = %d" l) frame_sites)
  in
  Printf.sprintf
    {ocaml|
(** Pops of tabulated caller frames — passive no-ops of the transfer set. *)
let last_passive_pops : int ref = ref 0

let step
    (aux :
      A.handle -> string -> A.kidx -> D.t list -> D.t option)
    (h : A.handle) (sigma : A.state) ((phi, k) : A.Key.t) (rho : A.aenv)
    (kont : A.kont) : A.succ list =
  let l = Retargeting.Partition.lab phi in
  if l = %d then List.rev (seg_init aux h k kont rho)
  else if l = %d then List.rev (seg_entry aux h k kont rho)
  else if %s then return_all aux h sigma phi k rho kont
  else if %s then begin incr last_passive_pops; [] end
  else []

(** Analyze a T program with the STORED specialized transfer over (D, A); seeding,
    solving, widening, scheduling, and result read-out are A's own code. *)
let analyze_t
    ~(aux : A.handle -> string -> A.kidx -> D.t list -> D.t option)
    ?(arg : D.t = D.int_lit 0) (p : Retargeting.T_encoding.program) :
    A.analysis =
  A.analyze_t_with ~step:(step aux) ~arg p
|ocaml}
    main_l eval_entry ret_disj frame_disj

(* the glue of the auxiliary-denotations arm: the leak is a runtime bool
   (false = the specialized cut-limited transfer, true = the paper-faithful
   transfer), heads are main + eval-entry, non-head pops are passive. *)
let glue_text_f : string =
  let ret_disj =
    String.concat " || "
      (List.map (fun (l, _) -> Printf.sprintf "l = %d" l) ret_sites)
  in
  Printf.sprintf
    {ocaml|
let heads_f : Retargeting.Label.Set.t =
  Retargeting.Label.Set.of_list [ %d; %d ]

let step_f
    (aux :
      A.handle -> string -> A.kidx -> D.t list -> D.t option)
    (leak : bool) (h : A.handle) (sigma : A.state) ((phi, k) : A.Key.t)
    (rho : A.aenv) (kont : A.kont) : A.succ list =
  let l = Retargeting.Partition.lab phi in
  if l = %d then List.rev (fseg_init aux leak h k kont phi rho)
  else if l = %d then List.rev (fseg_entry aux leak h k kont phi rho)
  else if %s then freturn_all aux leak h sigma phi k rho kont
  else begin incr last_passive_pops; [] end

(** The stored specialized (cut-limited) analysis (paper precision at cuts, no leak).
    [~exact:true] runs the designated instance: the residual routes every
    chain arrival through [A.partitions_of], so the per-ℓt splits and env pins
    threaded by [A.analyze_t_with ~exact] apply at every chain index (the
    stored exact-instance gates of tests/test_exact_disc.ml). *)
let analyze_t_fminus
    ~(aux : A.handle -> string -> A.kidx -> D.t list -> D.t option)
    ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : A.analysis =
  A.analyze_t_with
    ~step:(step_f aux false)
    ~passive:(Retargeting.Calc_pe.faithful_passive heads_f)
    ~exact ~arg p

(** The stored PAPER-FAITHFUL analysis (join-then-step + the leak). *)
let analyze_t_faithful
    ~(aux : A.handle -> string -> A.kidx -> D.t list -> D.t option)
    ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : A.analysis =
  A.analyze_t_with
    ~step:(step_f aux true)
    ~passive:(Retargeting.Calc_pe.faithful_passive heads_f)
    ~exact ~arg p

|ocaml}
    main_l eval_entry main_l eval_entry ret_disj

(* the analyzed-auxiliary arm's glue: no summary parameter (the
   leaves' [aux] binder is fed an inert dummy — no aux branch was generated),
   heads at main plus EVERY function entry, cut sets over the whole program *)
let glue_text_a : string =
  let ret_disj =
    String.concat " || "
      (List.map (fun (l, _) -> Printf.sprintf "l = %d" l) ret_sites_a)
  in
  let frame_disj =
    String.concat " || "
      (List.map (fun (l, _) -> Printf.sprintf "l = %d" l) frame_sites_a)
  in
  let head_disp =
    String.concat ""
      (List.map
         (fun l ->
           Printf.sprintf "  else if l = %d then List.rev (head_l%d dummy_aux h k kont rho)\n" l l)
         entry_heads_a)
  in
  Printf.sprintf
    {ocaml|
(** Pops of tabulated caller frames of the analyzed network. *)
let last_passive_pops : int ref = ref 0

let dummy_aux : A.handle -> string -> A.kidx -> D.t list -> D.t option =
 fun _ _ _ _ -> None

let step (h : A.handle) (sigma : A.state) ((phi, k) : A.Key.t) (rho : A.aenv)
    (kont : A.kont) : A.succ list =
  let l = Retargeting.Partition.lab phi in
  if l = %d then List.rev (seg_init dummy_aux h k kont rho)
%s  else if %s then return_all dummy_aux h sigma phi k rho kont
  else if %s then begin incr last_passive_pops; [] end
  else []

(** The stored analysis with the auxiliary summary inlined and analyzed. *)
let analyze_t ?(arg : D.t = D.int_lit 0) (p : Retargeting.T_encoding.program) :
    A.analysis =
  A.analyze_t_with ~step ~arg p
|ocaml}
    main_l head_disp ret_disj frame_disj

(* the glue of the analyzed-auxiliary arm *)
let glue_text_af : string =
  let ret_disj =
    String.concat " || "
      (List.map (fun (l, _) -> Printf.sprintf "l = %d" l) ret_sites_a)
  in
  let head_disp =
    String.concat ""
      (List.map
         (fun l ->
           Printf.sprintf
             "  else if l = %d then List.rev (fhead_l%d dummy_aux leak h k \
              kont phi rho)\n"
             l l)
         entry_heads_a)
  in
  let heads_list =
    String.concat "; "
      (List.map (Printf.sprintf "%d") (main_l :: entry_heads_a))
  in
  Printf.sprintf
    {ocaml|
let heads_f : Retargeting.Label.Set.t =
  Retargeting.Label.Set.of_list [ %s ]

let step_f (leak : bool) (h : A.handle) (sigma : A.state)
    ((phi, k) : A.Key.t) (rho : A.aenv) (kont : A.kont) : A.succ list =
  let l = Retargeting.Partition.lab phi in
  if l = %d then List.rev (fseg_init dummy_aux leak h k kont phi rho)
%s  else if %s then freturn_all dummy_aux leak h sigma phi k rho kont
  else begin incr last_passive_pops; [] end

(** The stored specialized (cut-limited) analysis with the auxiliary summary analyzed.
    [~exact:true] is the designated instance (the stored summary gate). *)
let analyze_t_fminus ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : A.analysis =
  A.analyze_t_with
    ~step:(step_f false)
    ~passive:(Retargeting.Calc_pe.faithful_passive heads_f)
    ~exact ~arg p

(** The stored paper-faithful analysis with the auxiliary summary analyzed. *)
let analyze_t_faithful ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : A.analysis =
  A.analyze_t_with
    ~step:(step_f true)
    ~passive:(Retargeting.Calc_pe.faithful_passive heads_f)
    ~exact ~arg p

|ocaml}
    heads_list main_l head_disp ret_disj

let () =
  let out = try Sys.argv.(1) with _ -> "generated_calc.ml" in
  let buf = Buffer.create (1 lsl 16) in
  let iprog_digest = Digest.to_hex (Digest.string (Marshal.to_string iprog [])) in
  Buffer.add_string buf
    (Printf.sprintf
       "(* GENERATED by staging/calc_stage.ml — the STORED specialized analyzer\n\
       \   (the specialized langt-transfer), partially evaluated w.r.t. the\n\
       \   interpreter text I_S^T: one residual per segment head (init /\n\
       \   eval-entry dispatch) plus the return arm with the caller-site\n\
       \   resume dispatch emitted once; the auxiliary operator is a parameter\n\
       \   (the auxiliary denotations or the sub-fixpoint summary). The table /\n\
       \   worklist / widen / scope runtime is A's own\n\
       \   (the residual plugs into A.solve through A.analyze_t_with). Do not edit.\n\
       \   provenance: I_S^T digest = %s; regenerate via scripts/run-gen-calc.sh. *)\n\
        [@@@warning \"-a\"]\n\n\
        module Make\n\
       \    (D : Retargeting.Domain_intf.DOMAIN)\n\
       \    (A : module type of Retargeting.S_abstract.Make (D)) =\n\
        struct\n"
       iprog_digest);
  Buffer.add_string buf "let seg_init = ";
  Buffer.add_string buf (functor_rewrite (string_of_code (gen_head ~ax:is_aux main_l)));
  Buffer.add_string buf "\n\nlet seg_entry = ";
  Buffer.add_string buf
    (functor_rewrite (string_of_code (gen_head ~ax:is_aux eval_entry)));
  Buffer.add_string buf "\n\nlet return_all = ";
  Buffer.add_string buf
    (functor_rewrite
       (string_of_code
          (gen_return_all ~ax:is_aux ~rets:ret_sites ~frames:frame_sites)));
  Buffer.add_string buf "\n";
  Buffer.add_string buf glue_text;
  (* the paper-faithful / specialized-transfer emissions of the auxiliary-denotations arm *)
  Buffer.add_string buf "\nlet fseg_init = ";
  Buffer.add_string buf
    (functor_rewrite (string_of_code (gen_fhead ~ax:is_aux main_l)));
  Buffer.add_string buf "\n\nlet fseg_entry = ";
  Buffer.add_string buf
    (functor_rewrite (string_of_code (gen_fhead ~ax:is_aux eval_entry)));
  Buffer.add_string buf "\n\nlet freturn_all = ";
  Buffer.add_string buf
    (functor_rewrite
       (string_of_code
          (gen_freturn_all ~ax:is_aux ~rets:ret_sites ~frames:frame_sites)));
  Buffer.add_string buf "\n";
  Buffer.add_string buf glue_text_f;
  (* the analyzed-auxiliary arm: the transfer set stored as code *)
  let no_aux (_ : string) = false in
  Buffer.add_string buf "\nmodule Analyzed = struct\n";
  Buffer.add_string buf "let seg_init = ";
  Buffer.add_string buf
    (functor_rewrite (string_of_code (gen_head ~ax:no_aux main_l)));
  List.iter
    (fun l ->
      Buffer.add_string buf (Printf.sprintf "\n\nlet head_l%d = " l);
      Buffer.add_string buf
        (functor_rewrite (string_of_code (gen_head ~ax:no_aux l))))
    entry_heads_a;
  Buffer.add_string buf "\n\nlet return_all = ";
  Buffer.add_string buf
    (functor_rewrite
       (string_of_code
          (gen_return_all ~ax:no_aux ~rets:ret_sites_a ~frames:frame_sites_a)));
  Buffer.add_string buf "\n";
  Buffer.add_string buf glue_text_a;
  (* the paper-faithful / specialized-transfer emissions of the analyzed-auxiliary arm *)
  Buffer.add_string buf "\nlet fseg_init = ";
  Buffer.add_string buf
    (functor_rewrite (string_of_code (gen_fhead ~ax:no_aux main_l)));
  List.iter
    (fun l ->
      Buffer.add_string buf (Printf.sprintf "\n\nlet fhead_l%d = " l);
      Buffer.add_string buf
        (functor_rewrite (string_of_code (gen_fhead ~ax:no_aux l))))
    entry_heads_a;
  Buffer.add_string buf "\n\nlet freturn_all = ";
  Buffer.add_string buf
    (functor_rewrite
       (string_of_code
          (gen_freturn_all ~ax:no_aux ~rets:ret_sites_a ~frames:frame_sites_a)));
  Buffer.add_string buf "\n";
  Buffer.add_string buf glue_text_af;
  Buffer.add_string buf "end\n";
  Buffer.add_string buf "end\n\n";
  Buffer.add_string buf
    "module Default = Make (Retargeting.Domain_rtg) (Retargeting.S_abstract)\n";
  let oc = open_out out in
  output_string oc (Buffer.contents buf);
  close_out oc;
  Printf.printf "calc_stage: wrote %s (%d ret sites, %d frame sites)\n" out
    (List.length ret_sites) (List.length frame_sites)
