#!/usr/bin/env bash
#
# kick-tires.sh — quick check (~2-3 min): build, run one benchmark's concrete
# oracle, then a single low-sample replicate of the paper-table bench with its
# aggregation. Everything is working if this ends with the (rough) table printed
# and "kick-tires: OK".
#
# The full gate suite is `dune test` (README.md; ~15 min).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "== build =="
dune build --root .

echo
echo "== one faithful port vs. the concrete oracle =="
scripts/check-programs.sh programs/fx2_gcd.t

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
