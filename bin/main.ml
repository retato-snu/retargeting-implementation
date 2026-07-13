(** Entry point: one CLI that drives the artifact's execution paths.

    Subcommands:

      interp   <prog> [--arg N]                 run the S-coded T interpreter
               [I_S^T] on the concrete S-CEK machine — the concrete oracle,
               prints the decoded integer (scripts/check-programs.sh drives
               this over each program's `# case:` lines).
      analyze  <prog> [--exact] [--top | --arg N]
               run the BASE abstract interpreter [S_abstract] on [I_S^T] —
               prints the abstract root value, worklist pops, and table
               entries. --exact selects the designated paper instance
               (the table's b/s-x lane).
      run-spec <prog> [--aux summary|denotations] [--top | --arg N]
               run the STORED specialized analyzer
               (lib_gen/generated_calc.ml) at the designated paper instance:
                 --aux summary      = the gpm/s-x lane (analyzed auxiliaries)
                 --aux denotations  = the gpm/f-x lane (auxiliary denotations).
      stage    [--check]                        (re)generate — or, with
               --check, verify — lib_gen/generated_calc.ml. Delegates to
               scripts/run-gen-calc.sh (needs the BER MetaOCaml switch).

    <prog> is T concrete syntax, e.g. 'sq(x) = x * x; sq(4)'. The abstract
    lanes default to the unknown argument (top); [--arg N] pins a literal. *)

open Retargeting
module GC = Retargeting_gen.Gen_calc

let usage =
  "usage:\n\
  \  main interp   <prog> [--arg N]                     run I_S^T concretely (the oracle)\n\
  \  main analyze  <prog> [--exact] [--top | --arg N]   run the base analyzer (b/slow, --exact = b/s-x)\n\
  \  main run-spec <prog> [--aux summary|denotations]\n\
  \                       [--top | --arg N]             run the stored specialized analyzer (gpm/s-x, gpm/f-x)\n\
  \  main stage    [--check]                            (re)generate / verify lib_gen/generated_calc.ml\n\
  \n\
  \  <prog> is T concrete syntax, e.g. 'sq(x) = x * x; sq(4)'.\n\
  \  abstract lanes default to the unknown argument (top); --arg N pins a literal.\n"

(* ------------------------------------------------------------------ *)
(* Tiny argument parser: a positional <prog> plus --flags, order-free.  *)
(* ------------------------------------------------------------------ *)

let value_flags = [ "--arg"; "--aux" ]

(* returns (positional program option, value-flag table, bool-flag set) *)
let parse_args (toks : string list) =
  let prog = ref None in
  let vals = Hashtbl.create 8 in
  let bools = Hashtbl.create 8 in
  let rec go = function
    | [] -> ()
    | t :: rest when List.mem t value_flags -> (
        match rest with
        | v :: rest' -> Hashtbl.replace vals t v; go rest'
        | [] -> Printf.eprintf "main: %s needs a value\n" t; exit 2)
    | t :: rest when String.length t >= 2 && t.[0] = '-' && t.[1] = '-' ->
        Hashtbl.replace bools t (); go rest
    | t :: rest ->
        if !prog = None then prog := Some t;
        go rest
  in
  go toks;
  (!prog, vals, bools)

let get_prog prog sub =
  match prog with
  | Some s -> s
  | None -> Printf.eprintf "main %s: missing <prog>\n\n%s" sub usage; exit 2

(* the abstract argument for the analyzer lanes: --arg N pins a literal, else
   the unknown argument (top). *)
let abstract_arg vals =
  match Hashtbl.find_opt vals "--arg" with
  | Some n -> (
      match int_of_string_opt n with
      | Some k -> Domain_rtg.int_lit k
      | None -> Printf.eprintf "main: --arg expects an integer, got %S\n" n; exit 2)
  | None -> Domain_rtg.any_int

(* ------------------------------------------------------------------ *)
(* Lanes                                                               *)
(* ------------------------------------------------------------------ *)

let run_interp toks =
  let prog, vals, _ = parse_args toks in
  let p = T_parser.parse_program (get_prog prog "interp") in
  let arg =
    match Hashtbl.find_opt vals "--arg" with
    | Some n -> ( match int_of_string_opt n with Some k -> k | None -> 0)
    | None -> 0
  in
  Printf.printf "interp   (arg=%d)  => %d\n" arg (Interp_st.eval_t ~arg p)

let run_analyze toks =
  let prog, vals, bools = parse_args toks in
  let p = T_parser.parse_program (get_prog prog "analyze") in
  let exact = Hashtbl.mem bools "--exact" in
  let a = S_abstract.analyze_t ~exact ~arg:(abstract_arg vals) p in
  Printf.printf "analyze  %-7s  => %s   (pops %d, entries %d)\n"
    (if exact then "b/s-x" else "b/slow")
    (Domain_rtg.string_of_aint (Domain_rtg.root_int a.S_abstract.result))
    !S_abstract.last_solve_steps
    (S_abstract.table_size a.S_abstract.table)

let run_spec toks =
  let prog, vals, _ = parse_args toks in
  let p = T_parser.parse_program (get_prog prog "run-spec") in
  let arg = abstract_arg vals in
  let aux = Option.value ~default:"summary" (Hashtbl.find_opt vals "--aux") in
  let show label (a : Calc_pe.analysis) =
    let pops, passive, ent = !GC.last_stats in
    Printf.printf "run-spec %-8s => %s   (pops %d, entries %d)\n" label
      (Domain_rtg.string_of_aint (Domain_rtg.root_int a.Calc_pe.result))
      (pops - passive) ent
  in
  match aux with
  | "summary" ->
      show "gpm/s-x" (GC.analyze_t_fminus_analyzed ~exact:true ~arg p)
  | "denotations" | "denot" ->
      show "gpm/f-x" (GC.analyze_t_fminus ~exact:true ~arg p)
  | o ->
      Printf.eprintf "run-spec: unknown --aux %S (summary|denotations)\n" o;
      exit 2

let run_stage toks =
  let _, _, bools = parse_args toks in
  let cmd =
    "scripts/run-gen-calc.sh" ^ if Hashtbl.mem bools "--check" then " --check" else ""
  in
  exit (Sys.command cmd)

(* ------------------------------------------------------------------ *)
(* Dispatch                                                            *)
(* ------------------------------------------------------------------ *)

let () =
  let args = Array.to_list Sys.argv in
  let rest = match args with _ :: r -> r | [] -> [] in
  match rest with
  | "interp" :: toks -> run_interp toks
  | "analyze" :: toks -> run_analyze toks
  | "run-spec" :: toks -> run_spec toks
  | "stage" :: toks -> run_stage toks
  | ("help" | "-h" | "--help") :: _ | [] -> print_string usage
  | cmd :: _ ->
      Printf.eprintf "main: unknown subcommand %S\n\n%s" cmd usage;
      exit 2
