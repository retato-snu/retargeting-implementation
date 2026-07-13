(* Gen_calc: drivers for the STORED specialized analyzer.

   The specialized per-segment transfers live in the checked-in, generated
   functor {!Generated_calc.Make} (D)(A) (emitted from staging/calc_stage.ml);
   they plug into the base solver through [A.analyze_t_with] (the rtg domain) /
   [Ad.solve] (the disambiguated domain), so the fixpoint discipline is
   {!Retargeting.S_abstract}'s own. The auxiliary operator is the transfer's
   parameter: the auxiliary denotations ({!Retargeting.Domain_rtg.aux_denot} /
   [Domain_dis.Make.aux_denot]), or the auxiliary summary (the auxiliary
   bodies analyzed through the shared table).

   Each driver mirrors an in-process reference implementation in
   lib/calc_pe.ml; the gate (tests/test_gen_calc.ml) is result/table/pop
   equality against that reference. The paper's evaluation measures two of
   these drivers: {!analyze_t_fminus_analyzed} (summary) and
   {!analyze_t_fminus} (denotations), both at the designated instance. *)

module D = Retargeting.Domain_rtg
module A = Retargeting.S_abstract
module C = Retargeting.Calc_pe
module G = Generated_calc.Default

(** (worklist pops, passive frame pops, populated table entries) of the most
    recent analysis over the rtg domain ({!analyze_t}). *)
let last_stats : (int * int * int) ref = ref (0, 0, 0)

(* the auxiliary denotations: a closed form ignoring the handle and the
   stashed index (the denotation needs no T-context refinement — a fixed
   extension site), matching the in-process denotations arm *)
let fold_aux_rtg (_h : A.handle) (f : string) (_k : A.kidx) (args : D.t list) :
    D.t option =
  D.aux_denot f args

let run_rtg (aux : A.handle -> string -> A.kidx -> D.t list -> D.t option)
    (arg : D.t) (p : Retargeting.T_encoding.program) : C.analysis =
  G.last_passive_pops := 0;
  let a = G.analyze_t ~aux ~arg p in
  last_stats :=
    ( !A.last_solve_steps,
      !G.last_passive_pops,
      A.table_size a.A.table );
  { C.table = a.A.table; C.result = a.A.result }

(** The stored specialized analyzer over {!Domain_rtg} with the auxiliary
    denotations — the stored form of {!Retargeting.Calc_pe.analyze_t}. *)
let analyze_t ?(arg : D.t = D.int_lit 0) (p : Retargeting.T_encoding.program) :
    C.analysis =
  run_rtg fold_aux_rtg arg p

(** The specialized analyzer with the auxiliary summary inlined and analyzed
    (Generated_calc's [Analyzed] module): the stored form of
    {!Retargeting.Calc_pe.analyze_t_analyzed}. *)
let analyze_t_analyzed ?(arg : D.t = D.int_lit 0)
    (p : Retargeting.T_encoding.program) : C.analysis =
  Generated_calc.Default.Analyzed.last_passive_pops := 0;
  let a = Generated_calc.Default.Analyzed.analyze_t ~arg p in
  last_stats :=
    ( !A.last_solve_steps,
      !Generated_calc.Default.Analyzed.last_passive_pops,
      A.table_size a.A.table );
  { C.table = a.A.table; C.result = a.A.result }

(** The specialized cut-limited transfer and the paper-faithful transfer
    (Generated_calc's [step_f] leaves): the stored forms of
    {!Retargeting.Calc_pe}'s [analyze_t_fminus*] / [analyze_t_faithful*].
    Stats bookkeeping mirrors the in-process drivers (pops from the solve;
    passive from the module's counter; cells from the final table). *)

let run_stats (passive : int ref) (a : Retargeting.S_abstract.analysis) :
    C.analysis =
  last_stats := (!A.last_solve_steps, !passive, A.table_size a.A.table);
  { C.table = a.A.table; C.result = a.A.result }

let analyze_t_fminus_analyzed ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : C.analysis =
  let m = Generated_calc.Default.Analyzed.last_passive_pops in
  m := 0;
  run_stats m (Generated_calc.Default.Analyzed.analyze_t_fminus ~exact ~arg p)

let analyze_t_faithful_analyzed ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : C.analysis =
  let m = Generated_calc.Default.Analyzed.last_passive_pops in
  m := 0;
  run_stats m (Generated_calc.Default.Analyzed.analyze_t_faithful ~exact ~arg p)

let analyze_t_fminus ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : C.analysis =
  G.last_passive_pops := 0;
  run_stats G.last_passive_pops
    (G.analyze_t_fminus ~aux:fold_aux_rtg ~exact ~arg p)

let analyze_t_faithful ?(arg : D.t = D.int_lit 0) ?(exact = false)
    (p : Retargeting.T_encoding.program) : C.analysis =
  G.last_passive_pops := 0;
  run_stats G.last_passive_pops
    (G.analyze_t_faithful ~aux:fold_aux_rtg ~exact ~arg p)

(** (pops, passive, cells) of the most recent analysis over the
    disambiguated domain. *)
let last_stats_dis : (int * int * int) ref = ref (0, 0, 0)

(* the disambiguated-domain instance: the SAME stored transfers at the
   per-program disambiguated domain, seeded and driven exactly as the
   in-process reference Calc_pe.run_dis (Dd.prog_value seed, manual init,
   Ad.solve ~step) *)
let run_dis (arg : D.t) (p : Retargeting.T_encoding.program) : C.dis_analysis =
  let module Dd = Retargeting.Domain_dis.Make (struct
    let prog = p
  end) in
  let module Ad = Retargeting.S_abstract.Make (Dd) in
  let module Gd = Generated_calc.Make (Dd) (Ad) in
  let aux (_h : Ad.handle) (f : string) (_k : Ad.kidx) (args : Dd.t list) :
      Dd.t option =
    Dd.aux_denot f args
  in
  Gd.last_passive_pops := 0;
  let h = Ad.handle_for_interp () in
  let rho0 =
    Ad.initial_env (Dd.prog_value ()) (Dd.of_aint (D.root_int arg))
  in
  let phi0 = Ad.partition_of h h.Ad.prog.Retargeting.S_syntax.main rho0 in
  let init =
    Ad.Table.add (phi0, Ad.KBullet)
      { Ad.rho = rho0; Ad.kont = Ad.kont_halt }
      Ad.state_empty
  in
  let table = Ad.solve ~step:(Gd.step aux) h init in
  last_stats_dis :=
    (!Ad.last_solve_steps, !Gd.last_passive_pops, Ad.table_size table);
  {
    C.result = Dd.root_int (Ad.read_result h table);
    C.pops = !Ad.last_solve_steps;
    C.passive = !Gd.last_passive_pops;
    C.cells = Ad.table_size table;
  }

(** The stored specialized analyzer at the disambiguated domain with the
    auxiliary denotations — the stored form of
    {!Retargeting.Calc_pe.analyze_t_dis}. *)
let analyze_t_dis ?(arg : D.t = D.int_lit 0)
    (p : Retargeting.T_encoding.program) : C.dis_analysis =
  run_dis arg p
