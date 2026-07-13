# Benchmark artifact: retargeting a static analyzer to a new language

This branch is the measurement, and nothing else. It builds the three analyzers
the paper's evaluation table (`tab:impl-measure`) compares, runs them over the
thirteen benchmark programs, and prints the table.

The full artifact — the gates that pin the paper's correctness claims (the
projection is the target machine's own run; the derived segmentation is the
paper's factorization table; the stored analyzer computes what the in-process
one computes; the specialized analyzer equals the base on every program) — is on
the `artifact/impl-measure` branch. Nothing here is removed from the analyzers
themselves; only the test suite is.

## Requirements

- **OCaml 4.14.1** with **dune ≥ 3.0** (no libraries beyond the bundled `unix`).
- Linux with `taskset` for the timing runs (the scripts fall back to unpinned).
- Only to *regenerate* the stored specialized analyzer: **BER MetaOCaml N114**.
  The generated code is checked in, so nothing else needs it.

## Run it

```
scripts/kick-tires.sh        # ~2 min: build, one program through all lanes, rough table
scripts/check-programs.sh    # every program reproduces its declared `# case:` values
scripts/reproduce-table.sh   # ~5 min: the table, 3 replicates on a pinned core
```

`reproduce-table.sh` takes three process replicates on a pinned core (default
core 2, `CORE=n` to change), each the median of up to 15 samples per cell after
two warm-ups, and prints the per-cell median over the replicates with speedups
and their geometric means. Expected (Intel Xeon Silver 4314, OCaml 4.14.1):

| | specialized | specialized + auxiliary operators |
|---|---|---|
| geometric-mean speedup vs. base | ×1.16 | ×4.06 |
| per-program | faster on all 13 | ×1.17 – ×95 |

Absolute milliseconds are machine-dependent; the speedup ratios are the claim.
The **worklist-pop counters** the bench prints are machine-independent and must
match the recorded replicates (`docs/data/bench-paper-rep{1,2,3}.tsv`) exactly —
they are the check that your run analyzed the same thing. Aggregate the recorded
replicates with

```
dune exec bin/paper_table.exe -- docs/data/bench-paper-rep*.tsv
```

Building with a flambda compiler (`-O3`) makes every lane 4–6% faster and leaves
the speedups where they are, so the artifact targets a plain OCaml 4.14.1.

## The three lanes

| TSV key | table column | what runs |
|---|---|---|
| `b/s-x` | base | the generic S abstract interpreter (`lib/analysis/s_abstract.ml`) run on the S-coded interpreter `I_S^T` |
| `gpm/s-x` | specialized | the stored specialized analyzer, auxiliary functions analyzed |
| `gpm/f-x` | specialized + operators | the stored specialized analyzer, auxiliary denotations substituted |

All three run at the paper's designated instance (`~exact:true`). A single
program by hand:

```
P="$(grep -v '^ *#' programs/fx2_gcd.t | tr '\n' ' ')"
dune exec bin/main.exe -- interp   "$P" --arg 21               # concrete oracle
dune exec bin/main.exe -- analyze  "$P" --exact                # base
dune exec bin/main.exe -- run-spec "$P" --aux summary          # specialized
dune exec bin/main.exe -- run-spec "$P" --aux denotations      # + operators
```

The bench re-checks, on every measured program, that each specialized lane's
result agrees with the base's, and prints the relation.

## The programs

The thirteen rows of the table live in `programs/`: ten ports of first-order
kernels (`fx2_*`) plus `sai_fib`, `algo_fact_deep`, `algo_power2`. Provenance and
the per-program adaptations are in `docs/benchmarks.md` and in each file's header.
Each file's `# case:` lines record the concrete input/output pairs, which
`bin/main.exe interp` reproduces.

`fx2_solovay.t` is a fourteenth port, excluded from the table: its *base* cell
alone exceeds the 10 s per-cell budget. `scripts/reproduce-table.sh
--include-solovay` measures it anyway (the base cell reports as truncated).

## Layout

```text
lib/s/           the source language S — the language an analyzer already exists
                 for: syntax, parser, concrete CEK machine
lib/t/           the target language T: syntax, parser, the encoding of T
                 entities as S values, and T's concrete machine (the oracle)
lib/interp_st.ml I_S^T — T's interpreter WRITTEN AS AN S PROGRAM. Running the S
                 analyzer on it yields the base analyzer for T
lib/domain/      the value domains the analyzer is a functor over
lib/analysis/    the generic S abstract interpreter, and the retargeting that
                 recovers T's machine structure from it
lib/specialize/  the specialized analyzer, computed in process

staging/calc_stage.ml      the generator (BER MetaOCaml) that emits the
                           specialized analyzer as code
lib_gen/generated_calc.ml  the STORED specialized analyzer — machine-written,
                           do not edit. This is what the measurement runs
lib_gen/gen_calc.ml        drivers for the stored analyzer

bin/       main.ml (CLI), bench_paper.ml (the table's harness),
           paper_table.ml (replicate aggregation)
programs/  the benchmark programs
scripts/   kick-tires.sh, check-programs.sh, reproduce-table.sh, run-gen-calc.sh
docs/      benchmark provenance and the recorded measurement data
```

The stored analyzer is regenerable byte-identically (needs `metaocamlc`):

```
scripts/run-gen-calc.sh --check   # prints OK if the checked-in file is current
```
