(* Print the mechanically derived rule structure of the specialized analyzer.

   Standalone; run via `dune exec bin/calc_rules.exe`. Prints:
   - the derived segmentation of I_S^T (the derived langt-transfer rules): one
     row per segment, with the S-rule chain, the cut it stops at, and the
     caller-saved live set (the β_ℓ support);
   - the paper-name legend (the paper's rule names are mnemonics; the
     derivation only knows starts/sites);
   - the per-frame comparison against the paper's context bindings β_ℓ as
     extracted by Projection.Points (payload vars vs derived live sets). *)

open Retargeting
module DV = Calc_pe.Derive

(* The paper's mnemonic for each mechanical segment name (tab:macro): a
   reading aid only — nothing in the derivation consumes it. *)
let paper_name = function
  | "init" -> "Init (+ main glue)"
  | "entry/Int" -> "Int"
  | "entry/Var" -> "Var"
  | "entry/Sub" -> "Sub1"
  | "entry/Mul" -> "Mul1"
  | "entry/Let" -> "Let1"
  | "entry/App" -> "App1"
  | "entry/Ifz" -> "Ifz1"
  | "resume@Sub#1" -> "Sub2"
  | "resume@Sub#2" -> "Subr"
  | "resume@Mul#1" -> "Mul2"
  | "resume@Mul#2" -> "Mulr"
  | "resume@Let#1" -> "Let2"
  | "resume@Let#2" -> "Restore (let)"
  | "resume@App#1" -> "App2 (+ x0 glue)"
  | "resume@App#2" -> "Restore (app)"
  | "resume@Ifz#1/True" -> "Ifz2"
  | "resume@Ifz#1/False" -> "Ifz3"
  | "resume@Ifz#2" -> "Silent (then)"
  | "resume@Ifz#3" -> "Silent (else)"
  | "resume@root" -> "(halt)"
  | _ -> "?"

let () =
  let segs = DV.derive () in
  print_endline
    "Derived segmentation of I_S^T (cuts forced by the base transfer's table \
     reads;";
  print_endline
    "auxiliary calls folded under the Role_pe certificate) — the derived \
     langt-transfer rules:\n";
  List.iter
    (fun (s : DV.segment) ->
      Printf.printf "  %-22s %s\n"
        ("[" ^ paper_name s.DV.name ^ "]")
        (DV.string_of_segment s))
    segs;

  print_endline
    "\nFrame payloads: paper β_ℓ (Projection.Points) vs derived live sets:\n";
  let pts = Projection.points in
  let payload = function
    | Projection.Points.FAdd1 e2 -> ("Add1", [ e2 ])
    | Projection.Points.FAdd2 v1 -> ("Add2", [ v1 ])
    | Projection.Points.FSub1 e2 -> ("Sub1", [ e2 ])
    | Projection.Points.FSub2 v1 -> ("Sub2", [ v1 ])
    | Projection.Points.FMul1 e2 -> ("Mul1", [ e2 ])
    | Projection.Points.FMul2 v1 -> ("Mul2", [ v1 ])
    | Projection.Points.FDiv1 e2 -> ("Div1", [ e2 ])
    | Projection.Points.FDiv2 v1 -> ("Div2", [ v1 ])
    | Projection.Points.FMod1 e2 -> ("Mod1", [ e2 ])
    | Projection.Points.FMod2 v1 -> ("Mod2", [ v1 ])
    | Projection.Points.FLt1 e2 -> ("Lt1", [ e2 ])
    | Projection.Points.FLt2 v1 -> ("Lt2", [ v1 ])
    | Projection.Points.FLet (x, e2) -> ("Let", [ x; e2 ])
    | Projection.Points.FApp f -> ("App", [ f ])
    | Projection.Points.FApp2_1 (f, e2) -> ("App2_1", [ f; e2 ])
    | Projection.Points.FApp2_2 (f, v1) -> ("App2_2", [ f; v1 ])
    | Projection.Points.FApp3_1 (f, e2, e3) -> ("App3_1", [ f; e2; e3 ])
    | Projection.Points.FApp3_2 (f, v1, e3) -> ("App3_2", [ f; v1; e3 ])
    | Projection.Points.FApp3_3 (f, v1, v2) -> ("App3_3", [ f; v1; v2 ])
    | Projection.Points.FRestore env -> ("Restore", [ env ])
    | Projection.Points.FIfz (e2, e3) -> ("Ifz", [ e2; e3 ])
    | Projection.Points.FSilent -> ("Silent", [])
  in
  List.iter
    (fun (l, fk) ->
      let kind, vars = payload fk in
      let derived =
        List.filter_map
          (fun (s : DV.segment) ->
            match s.DV.site with
            | Some sl when Label.equal sl l -> Some s.DV.reads
            | _ -> None)
          segs
        |> List.fold_left DV.SS.union DV.SS.empty
      in
      Printf.printf "  site@%-3d %-8s β = {%s}   derived live = {%s}\n" l kind
        (String.concat "," vars)
        (String.concat "," (DV.SS.elements derived)))
    pts.Projection.Points.call_frames;
  print_endline
    "\n(deltas: env/defs threading appears in the live sets because the S \
     image reads the\n\
     environment from the caller's saved frame; the Restore payload is dead \
     for the\n\
     transfer — the paper's state-threaded environment (lem:brack) is supplied \
     by hand, not\n\
     recovered by this derivation.)"
