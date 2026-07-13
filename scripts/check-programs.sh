#!/usr/bin/env bash
#
# check-programs.sh [file.t ...] — check that the benchmark programs compute
# what they claim to. Every "# case: arg=N => V" line of a program is its
# concrete oracle; this runs each one through the S-coded interpreter I_S^T
# (`bin/main.exe interp`) and compares the result.
#
# With no arguments, checks every program in programs/.
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.."

dune build --root . bin/main.exe
MAIN=./_build/default/bin/main.exe

files=("$@")
if [ ${#files[@]} -eq 0 ]; then files=(programs/*.t); fi

total_fail=0
for f in "${files[@]}"; do
  echo "== $f"
  prog=$(grep -v '^[[:space:]]*#' "$f" | grep -v '^[[:space:]]*$' | tr '\n' ' ')
  if [ -z "$prog" ]; then echo "  NO PROGRAM LINE"; total_fail=1; continue; fi
  fail=0
  ncase=0
  while IFS= read -r line; do
    arg=$(echo "$line" | sed -n 's/.*arg=\(-\?[0-9]*\).*/\1/p')
    exp=$(echo "$line" | sed -n 's/.*=>[[:space:]]*\(-\?[0-9]*\).*/\1/p')
    [ -z "$arg" ] && continue
    ncase=$((ncase + 1))
    out=$("$MAIN" interp "$prog" --arg "$arg" 2>&1)
    got=$(echo "$out" | sed -n 's/.*=>[[:space:]]*\(-\?[0-9]*\).*/\1/p')
    if [ "$got" = "$exp" ]; then
      echo "  PASS arg=$arg => $exp"
    else
      echo "  FAIL arg=$arg expected=$exp got=[$out]"
      fail=1
    fi
  done < <(grep '# case:' "$f")
  if [ "$ncase" = 0 ]; then echo "  NO CASES"; fail=1; fi
  [ "$fail" = 0 ] || total_fail=1
done

if [ "$total_fail" = 0 ]; then echo "ALL PROGRAMS PASS"; else echo "FAILURES"; fi
exit $total_fail
