(* paper_table.ml — aggregate bench_paper replicate TSVs into the paper's
   evaluation table (tab:impl-measure).

     dune exec bin/paper_table.exe -- REP.tsv [REP.tsv ...]

   Per cell (program x engine) the value is the MEDIAN of the replicate
   medians (the paper uses three replicates); speedups are base/lane, the
   final row is the geometric mean of the per-program speedups. Reads both
   fresh bench_paper output and the recorded runs
   docs/data/bench-paper-rep{1,2,3}.tsv (same format; the
   `suite` column is ignored). *)

let table_order =
  [
    "gcd"; "ackermann"; "collatz"; "mccarthy91"; "tak"; "lattice"; "church";
    "fermat"; "rsa"; "mbrotz"; "fib"; "fact"; "power2";
  ]

let lanes = [ "b/s-x"; "gpm/s-x"; "gpm/f-x" ]

(* (program, engine) -> replicate medians (ms), in file order *)
let cells : (string * string, float list) Hashtbl.t = Hashtbl.create 64

let seen_programs : string list ref = ref []

(* the recorded replicates name the faithful ports with a -fx suffix
   (gcd-fx, ...); the paper table (and bench_paper) uses the plain family
   name — normalize *)
let normalize program =
  match Filename.chop_suffix_opt ~suffix:"-fx" program with
  | Some p -> p
  | None -> program

let add_row program engine med =
  let program = normalize program in
  if not (List.mem program !seen_programs) then
    seen_programs := !seen_programs @ [ program ];
  let k = (program, engine) in
  let old = try Hashtbl.find cells k with Not_found -> [] in
  Hashtbl.replace cells k (old @ [ med ])

let read_tsv path =
  let ic = open_in path in
  (try
     while true do
       let line = input_line ic in
       match String.split_on_char '\t' line with
       | "suite" :: _ -> () (* header *)
       | _ :: program :: engine :: med :: _ when List.mem engine lanes -> (
           match float_of_string_opt med with
           | Some m when m > 0. -> add_row program engine m
           | _ -> () (* T/O or malformed: leave the cell absent *))
       | _ -> ()
     done
   with End_of_file -> ());
  close_in ic

let median (xs : float list) : float =
  let a = Array.of_list xs in
  Array.sort compare a;
  let n = Array.length a in
  if n mod 2 = 1 then a.(n / 2) else (a.((n / 2) - 1) +. a.(n / 2)) /. 2.

let cell program engine : float option =
  match Hashtbl.find_opt cells (program, engine) with
  | Some (_ :: _ as xs) -> Some (median xs)
  | _ -> None

(* the paper's number format: three significant digits *)
let fmt_ms = function
  | None -> "-"
  | Some x ->
      if x >= 100. then Printf.sprintf "%.0f" x
      else if x >= 10. then Printf.sprintf "%.1f" x
      else Printf.sprintf "%.2f" x

let fmt_ratio = function
  | None -> "-"
  | Some r -> Printf.sprintf "x%.2f" r

let () =
  let files =
    match Array.to_list Sys.argv with
    | _ :: (_ :: _ as fs) -> fs
    | _ ->
        prerr_endline "usage: paper_table REP.tsv [REP.tsv ...]";
        exit 2
  in
  List.iter read_tsv files;
  let programs =
    List.filter (fun p -> List.mem p !seen_programs) table_order
    @ List.filter (fun p -> not (List.mem p table_order)) !seen_programs
  in
  let reps =
    List.fold_left
      (fun acc p ->
        match Hashtbl.find_opt cells (p, "b/s-x") with
        | Some xs -> max acc (List.length xs)
        | None -> acc)
      0 programs
  in
  Printf.printf
    "tab:impl-measure — median time (ms) over %d replicate(s); speedup vs. \
     the base\n\n"
    reps;
  Printf.printf "%-12s %10s %10s %10s   %9s %9s\n" "program" "base" "summary"
    "denot." "summary" "denot.";
  print_endline (String.make 68 '-');
  let ratios =
    List.map
      (fun p ->
        let base = cell p "b/s-x" in
        let s = cell p "gpm/s-x" in
        let f = cell p "gpm/f-x" in
        let r a b =
          match (a, b) with Some a, Some b -> Some (a /. b) | _ -> None
        in
        let rs = r base s and rf = r base f in
        Printf.printf "%-12s %10s %10s %10s   %9s %9s\n" p (fmt_ms base)
          (fmt_ms s) (fmt_ms f) (fmt_ratio rs) (fmt_ratio rf);
        (rs, rf))
      programs
  in
  let geomean sel =
    let xs = List.filter_map sel ratios in
    match xs with
    | [] -> None
    | xs ->
        Some
          (exp
             (List.fold_left (fun a x -> a +. log x) 0. xs
             /. float_of_int (List.length xs)))
  in
  print_endline (String.make 68 '-');
  Printf.printf "%-12s %10s %10s %10s   %9s %9s\n" "geo. mean" "" "" ""
    (fmt_ratio (geomean fst))
    (fmt_ratio (geomean snd))
