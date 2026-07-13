#!/usr/bin/env bash
#
# kick-tires.sh — quick check (~2 min): build, run one benchmark through the
# concrete oracle and the three measured analyzers, then one low-sample
# replicate of the paper-table bench with its aggregation. Everything is
# working if this ends with the (rough) table printed and "kick-tires: OK".
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "== build =="
dune build --root .

echo
echo "== gcd (arg=21) through all four lanes; all three analyses must contain 3 =="
P="$(grep -v '^ *#' programs/fx2_gcd.t | tr '\n' ' ')"
./_build/default/bin/main.exe interp   "$P" --arg 21
./_build/default/bin/main.exe analyze  "$P" --exact --arg 21
./_build/default/bin/main.exe run-spec "$P" --aux summary     --arg 21
./_build/default/bin/main.exe run-spec "$P" --aux denotations --arg 21

echo
echo "== paper-table bench, 1 replicate x 3 samples (rough) =="
OUT=outputs/kick-tires
mkdir -p "$OUT"
rm -f "$OUT"/rep1.tsv
./_build/default/bin/bench_paper.exe --iters 3 --tsv "$OUT/rep1.tsv"
echo
./_build/default/bin/paper_table.exe "$OUT/rep1.tsv"

echo
echo "kick-tires: OK"
