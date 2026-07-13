#!/usr/bin/env bash
#
# reproduce-table.sh — reproduce the paper's evaluation table
# (tab:impl-measure): REPS process replicates of the paper-table bench
# (median of up to ITERS samples per cell, two warm-ups) on a pinned core,
# then the per-cell median-of-medians table with speedups and geometric
# means.
#
# Environment knobs:
#   REPS=3    replicates (the paper uses 3)
#   ITERS=15  timing samples per cell (the paper uses 15)
#   CORE=2    core to pin with taskset (unset taskset -> unpinned)
#
# Extra arguments are passed to bench_paper (e.g. --include-solovay).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

REPS="${REPS:-3}"
ITERS="${ITERS:-15}"
CORE="${CORE:-2}"
OUT=outputs/paper-table
mkdir -p "$OUT"
rm -f "$OUT"/rep*.tsv

dune build --root . bin/bench_paper.exe bin/paper_table.exe

PIN=""
if command -v taskset >/dev/null 2>&1; then
  PIN="taskset -c $CORE"
  echo "pinning to core $CORE (CORE=n to change)"
else
  echo "taskset not found: running unpinned (expect more variance)"
fi

for i in $(seq 1 "$REPS"); do
  echo
  echo "== replicate $i/$REPS =="
  $PIN ./_build/default/bin/bench_paper.exe \
    --iters "$ITERS" --tsv "$OUT/rep$i.tsv" "$@"
done

echo
./_build/default/bin/paper_table.exe "$OUT"/rep*.tsv
echo
echo "replicate TSVs: $OUT/rep{1..$REPS}.tsv"
echo "the recorded replicates: docs/data/bench-paper-rep{1,2,3}.tsv"
