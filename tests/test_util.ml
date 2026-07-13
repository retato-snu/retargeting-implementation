(* Shared test infrastructure for the dependency-free test suite.

   This module holds the [check] assertion helper, the per-section banner, the
   thin parse wrappers over the S and T parsers, the shared sample programs
   (written as concrete syntax and parsed once), the depth-parameterized spine
   source-string generators, and the AST-navigation helpers the label-dependent
   tests rely on. Each concern-specific test module reuses these so the same
   programs and helpers are defined exactly once. *)

open Retargeting

(* A single test assertion: print [ok - name] when [cond] holds, otherwise print
   [FAIL - name] and abort the whole run with a non-zero exit. *)
let check name cond =
  if cond then Printf.printf "ok - %s\n" name
  else (
    Printf.printf "FAIL - %s\n" name;
    exit 1)

(* Print the closing banner for a section once all its checks have passed. *)
let banner msg = print_endline msg

(* {1 Parse helpers}

   Thin wrappers over the S and T parsers and the reference evaluators, so the
   tests read in terms of "parse this source and run it" rather than repeating
   the parser/evaluator plumbing. *)

(* Parse S surface text and run it on the S-CEK machine, returning the value. *)
let run_s src = S_cek.run_value (S_parser.parse src)

(* Parse a whole T program from concrete syntax. *)
let parse_t src = T_parser.parse_program src

(* Parse a single T expression in the empty (external-input) scope. *)
let parse_t_expr src = T_parser.parse_expr src

(* {1 Shared sample T programs}

   The abstract-interpreter and macro blocks run the same spread of T programs,
   so they are defined here once (as parsed values) and reused. The parser fixes
   the conventions these tests rely on: the function parameter and the main
   expression's free variable are the implicit id 0, let-bound ids are fresh,
   and function ids are assigned in definition order. *)

let arith = parse_t "(3 - 1) * 2"
let let_sub = parse_t "let x = 5 in x - 2"
let sq4 = parse_t "sq(x) = x * x; sq(4)"
let ifz_zero = parse_t "ifz (3 - 3) then 1 else 2"
let ifz_nonzero = parse_t "ifz (3 - 1) then 1 else 2"
let let_call_sub = parse_t "sq(x) = x * x; let y = 5 in sq(y) - 1"

(* Three subtractions nested as (a - b) - (c - d): an outer Sub whose two
   operands are themselves Subs. The two inner subtractions are evaluated at the
   same S eval-entry yet must land in distinct partitions keyed by their T label
   — the T-sensitivity property. Their labels are read off the parsed AST below
   rather than hardcoded. *)
let nested_sub = parse_t "(9 - 1) - (5 - 2)"

(* The labels the T-sensitivity tests need, derived structurally from
   [nested_sub]: the outer subtraction's label and the two inner subtractions'
   labels, in source order. Parsing "(a - b) - (c - d)" yields
   [Sub (outer, Sub (inner1, _, _), Sub (inner2, _, _))]. *)
let nested_sub_labels () =
  match nested_sub.T_encoding.main with
  | T_encoding.Sub
      (outer, T_encoding.Sub (inner1, _, _), T_encoding.Sub (inner2, _, _)) ->
      (outer, inner1, inner2)
  | _ -> failwith "nested_sub: expected (e - e) - (e - e)"

(* main = x0 returns the external input (the implicit id 0). *)
let id_prog = parse_t "x"

(* ifz over an unknown argument: both branches are live abstractly. *)
let ifz_arg = parse_t "ifz x then 100 else 200"

(* A recursive T function: f(x) = ifz x then 100 else f(x - 1). It bottoms out
   at the base case 100 regardless of the argument, which makes it a good
   termination/soundness probe (the recursion depth depends on the argument, so
   a naive unfolding would not terminate). *)
let rec_fun = parse_t "f(x) = ifz x then 100 else f(x - 1); f(x)"

(* The shared spread of T programs (name, parsed program) used by the
   differential, projection, abstract-interpreter, and macro tests. *)
let diff_programs : (string * T_encoding.program) list =
  [
    ("(3 - 1) * 2", arith);
    ("let x = 5 in x - 2", let_sub);
    ("sq(4)", sq4);
    ("ifz (3-3) then 1 else 2", ifz_zero);
    ("ifz (3-1) then 1 else 2", ifz_nonzero);
    ("main argument", id_prog);
    ("let + call + sub", let_call_sub);
    ("ifz over the argument", ifz_arg);
  ]

(* {1 Spine source-string generators}

   The spine regression needs depth-parameterized left-nested Sub / Mul spines.
   A parser does not generalize a depth family, so we generate the concrete T
   source string for depth [n] and parse it. The parser assigns sequential
   labels from 0 in a left-to-right traversal, exactly as a front-end would, so
   the parsed spine reproduces the conflated-caller-partition shape the
   regression exercises. *)

(* Left-nested Sub spine of [depth] subtractions over a leaf 0:
   (((0 - 1) - 1) - ...) with [depth] ones. Concrete result = -depth. *)
let sub_spine_src ~depth =
  let buf = Buffer.create 64 in
  for _ = 1 to depth do
    Buffer.add_string buf "("
  done;
  Buffer.add_string buf "0";
  for _ = 1 to depth do
    Buffer.add_string buf " - 1)"
  done;
  Buffer.contents buf

(* Left-nested Mul spine of [depth] multiplications over a leaf 1:
   (((1 * 2) * 2) * ...) with [depth] twos. Concrete result = 2^depth. *)
let mul_spine_src ~depth =
  let buf = Buffer.create 64 in
  for _ = 1 to depth do
    Buffer.add_string buf "("
  done;
  Buffer.add_string buf "1";
  for _ = 1 to depth do
    Buffer.add_string buf " * 2)"
  done;
  Buffer.contents buf
