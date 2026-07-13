(* Storage gate: the stored specialized engine ({!Retargeting_gen.Gen_calc},
   running the checked-in {!Retargeting_gen.Generated_calc} per-segment
   residuals through the base solver) reproduces its in-process reference
   implementation {!Retargeting.Calc_pe} exactly, arm by arm:

     - rtg fold      = Calc_pe.analyze_t          (result, FULL table, pops,
                                                   passive pops, cells)
     - dis fold      = Calc_pe.analyze_t_dis      (result, pops, passive, cells)

   Equality of the stored form with the in-process form is the storage claim;
   everything semantic about the in-process lanes (tab:macro coincidence, β,
   soundness) is already gated by test_calc_pe and is inherited through this
   equality. *)

open Retargeting
module A = S_abstract
module D = Domain_rtg
module C = Calc_pe
module G = Retargeting_gen.Gen_calc
open Test_util

let val_eq a b = D.leq a b && D.leq b a
let aint_eq a b = D.aint_leq a b && D.aint_leq b a

let entry_eq (a : A.entry) (b : A.entry) : bool =
  A.aenv_leq a.A.rho b.A.rho
  && A.aenv_leq b.A.rho a.A.rho
  && A.compare_kont a.A.kont b.A.kont = 0

let tables_eq (ta : A.state) (tb : A.state) : bool =
  A.Table.cardinal ta = A.Table.cardinal tb
  && A.Table.for_all
       (fun k va ->
         match A.Table.find_opt k tb with
         | Some vb -> entry_eq va vb
         | None -> false)
       ta

let check_cell (name : string) (p : T_encoding.program) (arg : D.t)
    (targ : string) : unit =
  let tag lane s = Printf.sprintf "gen-calc %s %s: %s (arg=%s)" lane s name targ in
  (* rtg, auxiliary denotations *)
  let c = C.analyze_t ~arg p in
  let c_pops, c_passive, c_cells = !C.last_stats in
  let g = G.analyze_t ~arg p in
  let g_pops, g_passive, g_cells = !G.last_stats in
  check (tag "retargeted / denotations" "result") (val_eq c.C.result g.C.result);
  check (tag "retargeted / denotations" "table") (tables_eq c.C.table g.C.table);
  check (tag "retargeted / denotations" "pops")
    ((g_pops, g_passive, g_cells) = (c_pops, c_passive, c_cells));
  (* rtg, the auxiliary summary (pure specialization arm) *)
  let ca = C.analyze_t_analyzed ~arg p in
  let ca_stats = !C.last_stats in
  let ga = G.analyze_t_analyzed ~arg p in
  let ga_stats = !G.last_stats in
  check (tag "retargeted / summary" "result") (val_eq ca.C.result ga.C.result);
  check (tag "retargeted / summary" "table") (tables_eq ca.C.table ga.C.table);
  check (tag "retargeted / summary" "pops") (ga_stats = ca_stats);
  (* rtg, the specialized (cut-limited) and paper-faithful transfers
     (auxiliary summary) — the stored forms *)
  let cfm = C.analyze_t_fminus_analyzed ~arg p in
  let cfm_stats = !C.last_stats in
  let gfm = G.analyze_t_fminus_analyzed ~arg p in
  let gfm_stats = !G.last_stats in
  check (tag "retargeted / specialized (cut-limited, summary)" "result") (val_eq cfm.C.result gfm.C.result);
  check (tag "retargeted / specialized (cut-limited, summary)" "table") (tables_eq cfm.C.table gfm.C.table);
  check (tag "retargeted / specialized (cut-limited, summary)" "pops") (gfm_stats = cfm_stats);
  let cpf = C.analyze_t_faithful_analyzed ~arg p in
  let cpf_stats = !C.last_stats in
  let gpf = G.analyze_t_faithful_analyzed ~arg p in
  let gpf_stats = !G.last_stats in
  check (tag "retargeted / paper-faithful (summary)" "result") (val_eq cpf.C.result gpf.C.result);
  check (tag "retargeted / paper-faithful (summary)" "table") (tables_eq cpf.C.table gpf.C.table);
  check (tag "retargeted / paper-faithful (summary)" "pops") (gpf_stats = cpf_stats);
  (* rtg, the specialized (cut-limited) and paper-faithful transfers
     (auxiliary denotations) *)
  let cfmf = C.analyze_t_fminus ~arg p in
  let cfmf_stats = !C.last_stats in
  let gfmf = G.analyze_t_fminus ~arg p in
  let gfmf_stats = !G.last_stats in
  check (tag "retargeted / specialized (cut-limited, denotations)" "result") (val_eq cfmf.C.result gfmf.C.result);
  check (tag "retargeted / specialized (cut-limited, denotations)" "table") (tables_eq cfmf.C.table gfmf.C.table);
  check (tag "retargeted / specialized (cut-limited, denotations)" "pops") (gfmf_stats = cfmf_stats);
  let cpff = C.analyze_t_faithful ~arg p in
  let cpff_stats = !C.last_stats in
  let gpff = G.analyze_t_faithful ~arg p in
  let gpff_stats = !G.last_stats in
  check (tag "retargeted / paper-faithful (denotations)" "result") (val_eq cpff.C.result gpff.C.result);
  check (tag "retargeted / paper-faithful (denotations)" "table") (tables_eq cpff.C.table gpff.C.table);
  check (tag "retargeted / paper-faithful (denotations)" "pops") (gpff_stats = cpff_stats);
  (* the PAPER-EXACT instance (~exact:true) on the two specialized lanes: the
     stored residual reproduces the in-process fold-exact and summary-exact
     lanes verbatim over the real domain (result + full table + pops) — the
     storage claim at the exact instance *)
  let cxf = C.analyze_t_fminus ~exact:true ~arg p in
  let cxf_stats = !C.last_stats in
  let gxf = G.analyze_t_fminus ~exact:true ~arg p in
  let gxf_stats = !G.last_stats in
  check (tag "retargeted / specialized (cut-limited, denotations, exact)" "result") (val_eq cxf.C.result gxf.C.result);
  check (tag "retargeted / specialized (cut-limited, denotations, exact)" "table") (tables_eq cxf.C.table gxf.C.table);
  check (tag "retargeted / specialized (cut-limited, denotations, exact)" "pops") (gxf_stats = cxf_stats);
  let cxm = C.analyze_t_fminus_analyzed ~exact:true ~arg p in
  let cxm_stats = !C.last_stats in
  let gxm = G.analyze_t_fminus_analyzed ~exact:true ~arg p in
  let gxm_stats = !G.last_stats in
  check (tag "retargeted / specialized (cut-limited, summary, exact)" "result") (val_eq cxm.C.result gxm.C.result);
  check (tag "retargeted / specialized (cut-limited, summary, exact)" "table") (tables_eq cxm.C.table gxm.C.table);
  check (tag "retargeted / specialized (cut-limited, summary, exact)" "pops") (gxm_stats = cxm_stats);
  (* dis, auxiliary denotations *)
  let cd = C.analyze_t_dis ~arg p in
  let gd = G.analyze_t_dis ~arg p in
  check (tag "disambiguated / denotations" "result") (aint_eq cd.C.result gd.C.result);
  check (tag "disambiguated / denotations" "pops")
    ((gd.C.pops, gd.C.passive, gd.C.cells) = (cd.C.pops, cd.C.passive, cd.C.cells))

let run () =
  banner
    "== gen_calc: the stored specialized analyzer = its in-process reference ==";
  let progs : (string * T_encoding.program) list =
    [
      ("(3-1)*2", arith);
      ("let x=5 in x-2", let_sub);
      ("sq(4)", sq4);
      ("let+call+sub", let_call_sub);
      ("nested sub", nested_sub);
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
  List.iter
    (fun (name, p) ->
      List.iter
        (fun arg -> check_cell name p (D.int_lit arg) (string_of_int arg))
        [ 0; 7 ];
      check_cell name p D.any_int "T")
    progs;
  banner "gen_calc tests passed"
