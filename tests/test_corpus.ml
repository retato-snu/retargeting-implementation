(* File-based corpus harness for the S and T toolchain.

   This module discovers test programs written as plain text files: the
   regression corpus under [tests/corpus/s/] ([.s], S surface syntax) and
   [tests/corpus/t/] ([.t], T surface syntax), and the benchmark programs the
   evaluation table measures, under [programs/]. It parses each through the real
   parser ({!S_parser.parse} / {!T_parser.parse_program} — no program is ever
   hand-built as an OCaml AST), and cross-checks every implementation against the
   others and against the expected value the file declares in its header. The
   benchmarks are swept too, so the claim that the specialized analyzer equals
   the base holds on exactly the programs the table reports.

   {2 File format}

   A program file is its surface source, preceded by a header made of one or more
   [#] comment lines (the S and T lexers have no comment syntax, so [#] lines are
   stripped before parsing — they exist only for the harness and the reader).
   Header directives:

     - [# expect: V]            the program's result is the value [V]
                                (for a [.t] program the implicit argument is 0).
     - [# case: arg=N => V]     repeatable; the [.t] program run with integer
                                argument [N] yields [V]. Use this for
                                parameterized / recursive T programs.

   A file uses EITHER one [# expect:] OR one-or-more [# case:] lines. Any line
   whose first non-blank character is [#] is a header line; all other lines are
   the program body. Blank header lines and free-text [#] comments are ignored.

   The value grammar [V] for [# expect:] (and the RHS of [# case:]) is:
     - an integer, possibly negative: [18], [-5];
     - a constructor value: [True()], [Pair(7, 7)], [Cons(1, Nil())] — nested
       constructors and integer leaves only. ([.t] results are always integers,
       so [.t] files use the integer form; the constructor form is only needed by
       the [.s] corpus, e.g. returning [Pair(7, 7)].)

   {2 Checks per file}

   For a [.s] file (single declared expected value):
     - parse it with {!S_parser.parse};
     - assert [S_cek.run_value] equals the declared value — this verifies the S
       interpreter [S_cek];
     - assert the direct-S abstract analysis ({!S_abstract.analyze_prog}, seeded at
       [main] with the empty environment) terminates and is sound:
       [Domain_rtg.mem (S_cek.run_value prog) result] holds — verifies the
       partitioned abstract interpreter on diverse direct data-structure programs.
   This exercises {!S_abstract} directly on closed S programs (lists, trees,
   recursion), complementing the [.t] corpus's exercise of [S_abstract] {e via}
   [I_S^T].

   For a [.t] file, for each [arg] case (a single [# expect:] is the case
   [arg=0]):
     - parse it with {!T_parser.parse_program};
     - assert [T_machine.run ~arg] equals the declared value — verifies the paper
       T machine;
     - assert [Interp_st.eval_t ~arg] equals [T_machine.run ~arg] — the key
       cross-check verifying the S-coded T interpreter [I_S^T], which (running on
       the S-CEK machine) exercises [S_cek] too;
     - assert [S_abstract.analyze_t ~arg] terminates and is sound:
       [Domain_rtg.mem (T_machine.run ~arg p) result] holds — verifies the S
       abstract interpreter [S_abstract];
     - assert the SPECIALIZED analyzer ({!Calc_pe.analyze_t_fminus_analyzed},
       the auxiliary summary — the lane the measurement reports) is sound and
       EQUALS [S_abstract.analyze_t ~arg] at the result level: the paper's
       decomposition lemma, gated at the real (widening) value domain on every
       corpus program.

   A parse error, a value mismatch, or an unsound / non-terminating analysis is a
   failure naming the file (via {!Test_util.check}, which aborts the run). *)

open Retargeting
open Test_util

(* {1 Locating the programs}

   The [deps] in [tests/dune] copy both directories into the build tree, and dune
   runs the test with the tests directory as the working directory, so the corpus
   is at [corpus/] and the benchmarks at [../programs]. The fallbacks let the
   binary also be run by hand from the repo root. *)

let find_dir (what : string) (candidates : string list) : string =
  match
    List.find_opt
      (fun d -> Sys.file_exists d && Sys.is_directory d)
      candidates
  with
  | Some dir -> dir
  | None ->
      failwith
        (Printf.sprintf "test_corpus: cannot find the %s directory (looked for %s)"
           what (String.concat ", " candidates))

(* Every corpus file with the given extension under [dir], sorted, full relative
   path. Dot-files are skipped: dune's cram machinery drops [.cram.*.t] named
   pipes alongside our [.t] data (it reads the [.t] suffix as a cram test), and
   those leading-dot entries are not corpus programs. *)
let files_with_ext (dir : string) (ext : string) : string list =
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir |> Array.to_list
    |> List.filter (fun f ->
           Filename.check_suffix f ext
           && String.length f > 0
           && f.[0] <> '.'
           && not (Sys.is_directory (Filename.concat dir f)))
    |> List.sort String.compare
    |> List.map (fun f -> Filename.concat dir f)
  else []

let read_file (path : string) : string =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* {1 Header parsing}

   Split a file into (header directives, program body). A line whose first
   non-blank character is ['#'] is a header line; everything else is body. We keep
   the body lines joined by newlines so multi-line programs parse unchanged. *)

let is_header_line (line : string) : bool =
  let n = String.length line in
  let i = ref 0 in
  while !i < n && (line.[!i] = ' ' || line.[!i] = '\t') do
    incr i
  done;
  !i < n && line.[!i] = '#'

(* Drop the leading [#] (and any whitespace around it) from a header line,
   returning its directive text. *)
let header_text (line : string) : string =
  let line = String.trim line in
  (* line starts with '#'; drop it and trim again. *)
  String.trim (String.sub line 1 (String.length line - 1))

let split_header (src : string) : string list * string =
  let lines = String.split_on_char '\n' src in
  let headers =
    List.filter_map
      (fun l -> if is_header_line l then Some (header_text l) else None)
      lines
  in
  let body =
    lines
    |> List.filter (fun l -> not (is_header_line l))
    |> String.concat "\n"
  in
  (headers, body)

(* A directive is "key: rest" — return (key, rest) if the [prefix] (e.g.
   ["expect"], ["case"]) is present, both trimmed. *)
let strip_prefix (prefix : string) (s : string) : string option =
  match String.index_opt s ':' with
  | Some i ->
      let key = String.trim (String.sub s 0 i) in
      if String.equal key prefix then
        Some (String.trim (String.sub s (i + 1) (String.length s - i - 1)))
      else None
  | None -> None

(* {1 Expected-value parsing}

   Parse the declared value grammar [V]: an integer, or a constructor value with
   integer / nested-constructor arguments. Returns an {!S_cek.value} so [.s]
   constructor results can be checked exactly; [.t] results are always integers. *)

exception Bad_value of string

let parse_value (s : string) : S_cek.value =
  let s = String.trim s in
  let n = String.length s in
  let pos = ref 0 in
  let peek () = if !pos < n then Some s.[!pos] else None in
  let skip_ws () =
    while !pos < n && (s.[!pos] = ' ' || s.[!pos] = '\t') do
      incr pos
    done
  in
  let rec value () : S_cek.value =
    skip_ws ();
    match peek () with
    | Some c when c = '-' || (c >= '0' && c <= '9') -> integer ()
    | Some c when c >= 'A' && c <= 'Z' -> ctor ()
    | _ -> raise (Bad_value (Printf.sprintf "unexpected value text: %S" s))
  and integer () : S_cek.value =
    let start = !pos in
    if peek () = Some '-' then incr pos;
    while !pos < n && s.[!pos] >= '0' && s.[!pos] <= '9' do
      incr pos
    done;
    let tok = String.sub s start (!pos - start) in
    (match int_of_string_opt tok with
    | Some i -> S_cek.VInt i
    | None -> raise (Bad_value (Printf.sprintf "bad integer: %S" tok)))
  and ctor () : S_cek.value =
    let start = !pos in
    while
      !pos < n
      && ((s.[!pos] >= 'A' && s.[!pos] <= 'Z')
         || (s.[!pos] >= 'a' && s.[!pos] <= 'z')
         || (s.[!pos] >= '0' && s.[!pos] <= '9')
         || s.[!pos] = '_')
    do
      incr pos
    done;
    let tag = String.sub s start (!pos - start) in
    skip_ws ();
    if peek () <> Some '(' then
      raise (Bad_value (Printf.sprintf "constructor %S without arguments ()" tag));
    incr pos;
    (* arguments *)
    skip_ws ();
    let args =
      if peek () = Some ')' then (incr pos; [])
      else begin
        let acc = ref [ value () ] in
        skip_ws ();
        while peek () = Some ',' do
          incr pos;
          acc := value () :: !acc;
          skip_ws ()
        done;
        skip_ws ();
        (match peek () with
        | Some ')' -> incr pos
        | _ ->
            raise
              (Bad_value (Printf.sprintf "constructor %S: missing ')'" tag)));
        List.rev !acc
      end
    in
    S_cek.VTag (tag, args)
  in
  let v = value () in
  skip_ws ();
  if !pos <> n then
    raise (Bad_value (Printf.sprintf "trailing text after value: %S" s));
  v

(* An integer-only expected value (for [.t] results, which are always integers). *)
let parse_int_value (s : string) : int =
  match parse_value s with
  | S_cek.VInt i -> i
  | v ->
      raise
        (Bad_value
           (Printf.sprintf "expected an integer, got %s" (S_cek.string_of_value v)))

(* {1 Header directive extraction} *)

(* The single [# expect: V] directive, if present. *)
let find_expect (headers : string list) : string option =
  List.find_map (strip_prefix "expect") headers

(* Find the byte index of the substring [needle] in [s], or [None]. *)
let find_substring (s : string) (needle : string) : int option =
  let n = String.length s and m = String.length needle in
  if m = 0 then Some 0
  else begin
    let rec go i =
      if i + m > n then None
      else if String.sub s i m = needle then Some i
      else go (i + 1)
    in
    go 0
  end

(* All [# case: arg=N => V] directives, as (N, V-string) pairs, in file order.
   The directive body is "arg=N => V": split on "=>", read "arg=N" on the left
   (its single '=' separates the literal [arg] from the integer), keep [V] on the
   right. *)
let find_cases (headers : string list) : (int * string) list =
  List.filter_map
    (fun h ->
      match strip_prefix "case" h with
      | None -> None
      | Some rest -> (
          match find_substring rest "=>" with
          | None -> failwith (Printf.sprintf "bad case directive (no '=>'): %S" h)
          | Some i ->
              let lhs = String.trim (String.sub rest 0 i) in
              let rhs =
                String.trim (String.sub rest (i + 2) (String.length rest - i - 2))
              in
              (* lhs is "arg=N": require the [arg=] prefix, parse the rest as int. *)
              let prefix = "arg=" in
              let pl = String.length prefix in
              if
                String.length lhs >= pl && String.sub lhs 0 pl = prefix
              then
                let narg = String.trim (String.sub lhs pl (String.length lhs - pl)) in
                match int_of_string_opt narg with
                | Some narg -> Some (narg, rhs)
                | None -> failwith (Printf.sprintf "bad case arg integer: %S" lhs)
              else failwith (Printf.sprintf "bad case directive (need 'arg='): %S" h)))
    headers

(* {1 Running a .s file} *)

let run_s_file (path : string) : int =
  let module D = Domain_rtg in
  let src = read_file path in
  let headers, body = split_header src in
  let name = Filename.basename path in
  let expected =
    match find_expect headers with
    | Some v -> parse_value v
    | None ->
        failwith
          (Printf.sprintf "%s: a .s file needs exactly one '# expect:' header" name)
  in
  let prog =
    try S_parser.parse body
    with S_parser.Parse_error msg ->
      failwith (Printf.sprintf "%s: parse error: %s" name msg)
  in
  (* (1) Verify S_cek: run the program, compare to the declared value. *)
  let actual = S_cek.run_value prog in
  check
    (Printf.sprintf "[s] %s : S_cek.run_value = %s" name
       (S_cek.string_of_value expected))
    (actual = expected);
  (* (2) Direct-S abstract analysis terminates (populated table) and is sound
     (over-approximates the concrete result). *)
  let table = S_abstract.analyze_prog prog in
  check
    (Printf.sprintf "[s] %s : S_abstract.analyze_prog terminates" name)
    (S_abstract.table_size table > 0);
  let result = S_abstract.prog_result prog table in
  check
    (Printf.sprintf "[s] %s : S_abstract direct-S sound (mem %s)" name
       (S_cek.string_of_value actual))
    (D.mem actual result);
  3

(* {1 Running a .t file} *)

(* The list of (arg, expected-int) cases a [.t] file declares: either its single
   [# expect: V] (as the case arg=0) or its [# case:] lines. *)
let t_cases (name : string) (headers : string list) : (int * int) list =
  match (find_expect headers, find_cases headers) with
  | Some v, [] -> [ (0, parse_int_value v) ]
  | None, ((_ :: _) as cs) -> List.map (fun (n, v) -> (n, parse_int_value v)) cs
  | Some _, _ :: _ ->
      failwith
        (Printf.sprintf "%s: use either '# expect:' or '# case:', not both" name)
  | None, [] ->
      failwith
        (Printf.sprintf "%s: a .t file needs a '# expect:' or '# case:' header" name)

let run_t_file (path : string) : int =
  let module D = Domain_rtg in
  let src = read_file path in
  let headers, body = split_header src in
  let name = Filename.basename path in
  let p =
    try T_parser.parse_program body
    with T_parser.Parse_error msg ->
      failwith (Printf.sprintf "%s: parse error: %s" name msg)
  in
  let cases = t_cases name headers in
  let checks = ref 0 in
  List.iter
    (fun (arg, expected) ->
      (* (1) T machine equals the declared value. *)
      let machine = T_machine.run ~arg p in
      check
        (Printf.sprintf "[t] %s (arg=%d) : T_machine.run = %d" name arg expected)
        (machine = expected);
      incr checks;
      (* (2) I_S^T agrees with the T machine (the key cross-check). *)
      let interp = Interp_st.eval_t ~arg p in
      check
        (Printf.sprintf "[t] %s (arg=%d) : Interp_st.eval_t = T_machine.run" name
           arg)
        (interp = machine);
      incr checks;
      (* (3) The abstract analysis terminates (returns a populated table) and is
         sound (over-approximates the concrete result). *)
      let a = S_abstract.analyze_t ~arg:(D.int_lit arg) p in
      check
        (Printf.sprintf "[t] %s (arg=%d) : S_abstract.analyze_t terminates" name
           arg)
        (S_abstract.table_size a.S_abstract.table > 0);
      incr checks;
      check
        (Printf.sprintf "[t] %s (arg=%d) : S_abstract sound (mem %d)" name arg
           machine)
        (D.mem (S_cek.VInt machine) a.S_abstract.result);
      incr checks;
      (* (4) The specialized analyzer (the cut-limited transfer with the
         auxiliary summary — the lane the measurement reports as [gpm/s-x])
         REPRODUCES THE BASE ANALYSIS EXACTLY, and is sound.

         This is the paper's decomposition lemma, gated at the real (widening)
         value domain. It holds because the base widens only at its reentrant
         points ({!S_abstract.reentrant_points}) — the very boundaries the
         specialized analyzer retains as its chain ends — and joins along the
         acyclic interior the specialization eliminates. Widening at those
         interior labels too (the coarser every-key schedule) would make the
         base strictly coarser than the specialized analyzer on the shapes where
         the interior values grow. *)
      let c = Calc_pe.analyze_t_fminus_analyzed ~arg:(D.int_lit arg) p in
      check
        (Printf.sprintf "[t] %s (arg=%d) : specialized (summary) sound (mem %d)"
           name arg machine)
        (D.mem (S_cek.VInt machine) c.Calc_pe.result);
      incr checks;
      check
        (Printf.sprintf
           "[t] %s (arg=%d) : specialized (summary) = S_abstract.analyze_t" name
           arg)
        (D.leq a.S_abstract.result c.Calc_pe.result
        && D.leq c.Calc_pe.result a.S_abstract.result);
      incr checks)
    cases;
  !checks

(* {1 Driver} *)

let run () =
  let s_dir = find_dir "corpus/s" [ "corpus/s"; "tests/corpus/s" ] in
  let t_dir = find_dir "corpus/t" [ "corpus/t"; "tests/corpus/t" ] in
  let bench_dir = find_dir "programs" [ "../programs"; "programs" ] in
  let s_files = files_with_ext s_dir ".s" in
  let t_files = files_with_ext t_dir ".t" @ files_with_ext bench_dir ".t" in
  (* Neither may be empty, or a misconfigured glob would silently pass. *)
  check "corpus: at least one .s program discovered" (s_files <> []);
  check "corpus: at least one .t program discovered" (t_files <> []);
  check "corpus: the benchmark programs are swept too"
    (files_with_ext bench_dir ".t" <> []);
  let s_checks = List.fold_left (fun acc f -> acc + run_s_file f) 0 s_files in
  let t_checks = List.fold_left (fun acc f -> acc + run_t_file f) 0 t_files in
  Printf.printf
    "corpus summary: %d .s files (%d checks), %d .t files (%d checks)\n"
    (List.length s_files) s_checks (List.length t_files) t_checks;
  banner "all file-based corpus tests passed"
