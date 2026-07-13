(* bench_paper.ml — the measurement harness behind the paper's evaluation
   table (tab:impl-measure): the base analyzer vs. the STORED specialized
   analyzer at the designated paper instance.

   Lanes (TSV `engine` key — paper column):

     b/s-x    — "base": the base abstract interpreter (lib/s_abstract.ml)
                at the designated instance (~exact:true);
     gpm/s-x  — "specialized, summary": the stored specialized analyzer
                (lib_gen/generated_calc.ml, generated from
                staging/calc_stage.ml), auxiliary operator = the analyzed
                summary. Gated equal to the base at the cut points on the
                artifact/impl-measure branch;
     gpm/f-x  — "specialized, denotations": the stored specialized analyzer
                with the auxiliary denotations substituted (sound, can
                sharpen precision — strictly finer on church and fermat).

   Programs: the 13 rows of the table — the ten fx2_* ports plus the
   single-argument fib / fact / power2, all under programs/ (provenance:
   docs/benchmarks.md; scripts/check-programs.sh runs their oracles).
   solovay is excluded from the table because its BASE cell exceeds the
   per-cell budget (one run > 13 s);
   pass --include-solovay to measure it anyway.

   Method (the paper's): per cell one stats run (result + counters), then
   timing by [time_cell] — two warm-ups, up to --iters samples (a sub-ms
   cell runs an inner repetition so one sample is >= ~0.5 ms), median and
   quartiles over the samples. The paper reports, per cell, the median over
   THREE such process replicates on a taskset-pinned core
   (scripts/reproduce-table.sh); aggregation: bin/paper_table.ml.

   TSV rows (--tsv, append mode) use the same format as the recorded
   measurement docs/data/bench-paper-rep{1,2,3}.tsv. *)

module A = Retargeting.S_abstract
module D = Retargeting.Domain_rtg
module C = Retargeting.Calc_pe
module GC = Retargeting_gen.Gen_calc
module T_parser = Retargeting.T_parser
module T_encoding = Retargeting.T_encoding

let corpus_dir = "programs"

let read_t_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  let body =
    String.split_on_char '\n' s
    |> List.filter (fun l -> String.length l = 0 || l.[0] <> '#')
    |> String.concat "\n"
  in
  T_parser.parse_program body

(* The paper table's rows, in table order: display name -> corpus file. *)
let manifest =
  [
    ("gcd", "fx2_gcd");
    ("ackermann", "fx2_ackermann");
    ("collatz", "fx2_collatz");
    ("mccarthy91", "fx2_mccarthy91");
    ("tak", "fx2_tak");
    ("lattice", "fx2_lattice");
    ("church", "fx2_church");
    ("fermat", "fx2_fermat");
    ("rsa", "fx2_rsa");
    ("mbrotz", "fx2_mbrotz");
    ("fib", "sai_fib");
    ("fact", "algo_fact_deep");
    ("power2", "algo_power2");
  ]

let solovay_row = ("solovay", "fx2_solovay")

(* One converged analysis, uniformized: the abstract-integer root result and
   the (worklist pops, table entries) counters of the run. *)
type run = { ai : Retargeting.Domain_intf.aint; steps : int; entries : int }

let engines : (string * (D.t -> T_encoding.program -> run)) list =
  [
    ( "b/s-x",
      fun arg p ->
        let a = A.analyze_t ~exact:true ~arg p in
        { ai = D.root_int a.A.result; steps = !A.last_solve_steps;
          entries = A.table_size a.A.table } );
    ( "gpm/s-x",
      fun arg p ->
        let a = GC.analyze_t_fminus_analyzed ~exact:true ~arg p in
        let s, pas, e = !GC.last_stats in
        { ai = D.root_int a.C.result; steps = s - pas; entries = e } );
    ( "gpm/f-x",
      fun arg p ->
        let a = GC.analyze_t_fminus ~exact:true ~arg p in
        let s, pas, e = !GC.last_stats in
        { ai = D.root_int a.C.result; steps = s - pas; entries = e } );
  ]

(* ------------------------------------------------------------------ *)
(* Timing (identical to the recorded runs' harness)                    *)
(* ------------------------------------------------------------------ *)

let now_ms () = Unix.gettimeofday () *. 1000.

type cell = { med : float; q1 : float; q3 : float; n : int; truncated : bool }

(* Two warm-ups (the first doubles as the estimate); inner repetition so a
   sample is >= ~0.5 ms; up to [samples] samples, shrunk to stay within
   [max_cell_ms]; median/quartiles over the samples. A cell whose single
   warm-up already exceeds the budget reports that one run, marked
   truncated. *)
let time_cell ~(samples : int) ~(max_cell_ms : float) (f : unit -> unit) : cell
    =
  let t0 = now_ms () in
  f ();
  let est = now_ms () -. t0 in
  if est >= max_cell_ms then
    { med = est; q1 = est; q3 = est; n = 1; truncated = true }
  else begin
    f ();
    let rep =
      if est <= 0.0005 then 1000
      else max 1 (int_of_float (ceil (0.5 /. est)))
    in
    let per_sample = max (est *. float_of_int rep) 0.0001 in
    let n = max 3 (min samples (int_of_float (max_cell_ms /. per_sample))) in
    let xs =
      Array.init n (fun _ ->
          let t0 = now_ms () in
          for _ = 1 to rep do
            f ()
          done;
          (now_ms () -. t0) /. float_of_int rep)
    in
    Array.sort compare xs;
    let q p = xs.(min (n - 1) (int_of_float (p *. float_of_int (n - 1)))) in
    { med = q 0.5; q1 = q 0.25; q3 = q 0.75; n; truncated = false }
  end

(* ------------------------------------------------------------------ *)
(* Driver                                                              *)
(* ------------------------------------------------------------------ *)

let () =
  let iters = ref 15 in
  let tsv = ref "" in
  let max_cell_ms = ref 10_000. in
  let with_solovay = ref false in
  let speclist =
    [
      ("--iters", Arg.Set_int iters, "N  samples per cell (default 15)");
      ("--tsv", Arg.Set_string tsv, "FILE  append machine-readable rows");
      ( "--max-cell-ms",
        Arg.Set_float max_cell_ms,
        "MS  per-cell time budget (default 10000)" );
      ( "--include-solovay",
        Arg.Set with_solovay,
        "  also measure solovay (fx2_solovay; its base cell exceeds the \
         budget — reported truncated, excluded from the paper table)" );
    ]
  in
  Arg.parse speclist
    (fun s -> raise (Arg.Bad ("unknown argument " ^ s)))
    "bench_paper [--iters N] [--tsv FILE] [--max-cell-ms MS] \
     [--include-solovay]";
  let manifest =
    if !with_solovay then manifest @ [ solovay_row ] else manifest
  in
  let progs =
    List.map
      (fun (disp, file) ->
        (disp, read_t_file (Filename.concat corpus_dir (file ^ ".t"))))
      manifest
  in
  let tsv_oc =
    if !tsv = "" then None
    else begin
      let existed = Sys.file_exists !tsv in
      let oc = open_out_gen [ Open_append; Open_creat ] 0o644 !tsv in
      if not existed then
        output_string oc
          "suite\tprogram\tengine\tmed_ms\tq1_ms\tq3_ms\tsamples\ttruncated\tsteps\tentries\trel\n";
      Some oc
    end
  in
  let arg = D.any_int in
  Printf.printf
    "paper table bench — %d samples/cell target, %.0f ms/cell budget\n\n"
    !iters !max_cell_ms;
  let keys = List.map fst engines in
  let hdr ?(rel = false) fmt_unit =
    Printf.printf "%-16s" ("program" ^ fmt_unit);
    List.iter (fun k -> Printf.printf " %9s" k) keys;
    if rel then Printf.printf "  rel";
    Printf.printf "\n%s\n" (String.make 60 '-')
  in
  let rows =
    List.map
      (fun (name, p) ->
        let outcomes =
          List.map
            (fun (k, f) ->
              let r = f arg p in
              let c =
                time_cell ~samples:!iters ~max_cell_ms:!max_cell_ms (fun () ->
                    ignore (f arg p))
              in
              (k, r, c))
            engines
        in
        (* precision of each specialized lane vs. the base lane's root:
           '=' equal, '<' strictly finer, '!' incomparable (soundness bug) *)
        let base_ai =
          match outcomes with (_, r, _) :: _ -> r.ai | [] -> assert false
        in
        let rel =
          String.concat ""
            (List.filteri
               (fun i _ -> i > 0)
               (List.map
                  (fun (_, r, _) ->
                    if D.aint_leq r.ai base_ai then
                      if D.aint_leq base_ai r.ai then "=" else "<"
                    else "!")
                  outcomes))
        in
        (name, outcomes, rel))
      progs
  in
  hdr ~rel:true " (med ms)";
  List.iter
    (fun (name, outcomes, rel) ->
      Printf.printf "%-16s" name;
      List.iter
        (fun (_, _, c) ->
          if c.truncated then Printf.printf " %8.0f>" c.med
          else Printf.printf " %9.3f" c.med)
        outcomes;
      Printf.printf "  %s\n" rel;
      flush stdout)
    rows;
  Printf.printf "\n-- worklist pops --\n";
  hdr " (steps)";
  List.iter
    (fun (name, outcomes, _) ->
      Printf.printf "%-16s" name;
      List.iter (fun (_, r, _) -> Printf.printf " %9d" r.steps) outcomes;
      Printf.printf "\n")
    rows;
  (match tsv_oc with
  | None -> ()
  | Some oc ->
      List.iter
        (fun (name, outcomes, rel) ->
          List.iter
            (fun (k, r, c) ->
              Printf.fprintf oc
                "%s\t%s\t%s\t%.4f\t%.4f\t%.4f\t%d\t%b\t%d\t%d\t%s\n" "paper"
                name k c.med c.q1 c.q3 c.n c.truncated r.steps r.entries rel)
            outcomes)
        rows;
      close_out oc);
  Printf.printf
    "\n(aggregate replicates into the paper table with bin/paper_table.exe)\n"
