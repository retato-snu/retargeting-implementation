#!/usr/bin/env bash
#
# run-gen-calc.sh — regenerate (or, with --check, verify) the STORED specialized
# analyzer lib_gen/generated_calc.ml.
#
# The specialized analyzer is emitted as code by staging/calc_stage.ml under the
# BER MetaOCaml switch (metaocamlc); the result is plain OCaml, checked into
# lib_gen/ and tested in-process by the ordinary `dune test`
# (tests/test_gen_calc.ml). BER is needed ONLY to regenerate.
#
# Usage:
#   scripts/run-gen-calc.sh           regenerate lib_gen/generated_calc.ml
#   scripts/run-gen-calc.sh --check   fail if the checked-in file is stale
#                                      (its content differs from a fresh run)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

CHECK=0
[ "${1:-}" = "--check" ] && CHECK=1

BYTE_OBJS="_build/default/lib/.retargeting.objs/byte"
CMA="_build/default/lib/retargeting.cma"
TARGET="lib_gen/generated_calc.ml"

WORK="_build/gen-calc"
rm -rf "$WORK"
mkdir -p "$WORK"
cp staging/calc_stage.ml "$WORK/"

echo "run-gen-calc: building the library (dune, byte) ..."
dune build --root . "$CMA" lib

echo "run-gen-calc: compiling the generator (metaocamlc) ..."
( cd "$WORK"
  metaocamlc -I "../../$BYTE_OBJS" -c calc_stage.ml
  metaocamlc -I "../../$BYTE_OBJS" "../../$CMA" calc_stage.cmo -o calc_stage )

echo "run-gen-calc: generating the residual (the macro as code) ..."
( cd "$WORK" && ./calc_stage generated_calc.ml )

if [ "$CHECK" -eq 1 ]; then
  if diff -u "$TARGET" "$WORK/generated_calc.ml"; then
    echo "run-gen-calc: OK — $TARGET is up to date."
  else
    echo "run-gen-calc: STALE — $TARGET differs from a fresh generation." >&2
    echo "  regenerate with: scripts/run-gen-calc.sh" >&2
    exit 1
  fi
else
  cp "$WORK/generated_calc.ml" "$TARGET"
  echo "run-gen-calc: wrote $TARGET"
fi
