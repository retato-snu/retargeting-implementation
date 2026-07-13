# Artifact: A Framework for Retargeting Static Program Analyzers to New Languages

This artifact accompanies the paper's implementation section: the base
analyzer obtained by running a generic S-language abstract interpreter on the
definitional interpreter `I_S^T`, and the **stored specialized analyzer**
mechanically partially evaluated from it. It reproduces the paper's
evaluation table (`tab:impl-measure`): median analysis times and speedups of
the specialized analyzer over the base on the 13-program native benchmark
suite, under the two auxiliary operators (summary / denotations).

## Requirements

- **OCaml 4.14.1** with **dune ≥ 3.0** (no external libraries beyond the
  bundled `unix`).
- Linux with `taskset` is recommended for the timing runs (the scripts fall
  back to unpinned execution).
- Optional, only to *regenerate* the stored specialized analyzer
  (`scripts/run-gen-calc.sh`): **BER MetaOCaml N114** (`metaocamlc`, an
  OCaml 4.14.1-based switch). The generated code is checked in
  (`lib_gen/generated_calc.ml`), so nothing else needs it.

## Kick the tires (~2-3 min)

```
scripts/kick-tires.sh
```

Builds everything, validates one faithful port against the concrete
interpreter, then runs one low-sample replicate of the paper-table bench and
prints the aggregated table. Absolute times will differ from the paper on
your machine; the *speedup* columns should already be close, and the
worklist-pop counters must match the recorded replicates exactly.

## The claims and how to check them

**C1 — the benchmark programs compute what they claim to.** Every program in
`programs/` carries its concrete oracle as `# case: arg=N => V` lines; each is
run through the S-coded interpreter `I_S^T` and compared:

```
scripts/check-programs.sh         # ends with ALL PROGRAMS PASS
```

**C2 — the specialized analyzer reproduces the base analysis.** With the
summary operator the specialized analyzer computes *exactly the same result* as
the base analyzer, on every program of the corpus, at the real (widening) value
domain.

This is exact rather than approximate because the base widens **only at its
reentrant points** — the function entries, calls and returns, computed from the
analyzed S program by `S_abstract.reentrant_points` — and joins along the
acyclic straight-line interior. Those reentrant points are precisely the chain
boundaries the specialized analyzer retains, so the two apply widening at the
same places; the interior labels the specialization composes away are acyclic,
so joining there still terminates. (Widening at every revisited label instead —
the coarser schedule — would make the base strictly coarser than the specialized
analyzer on the shapes where interior values grow.)

The gates. Each pins something the paper states; there are no other tests.

- `tests/test_corpus.ml` — over the whole program corpus, for every argument
  case: the concrete T machine equals the declared value, the S-coded
  interpreter `I_S^T` equals that machine (the bisimulation cross-check), the
  base analyzer is sound, and **the specialized analyzer (summary) is sound and
  equals the base**;
- `tests/test_projection.ml` — the projection `⌊·⌋` of an `I_S^T` run *is* the T
  machine's own run, state by state, and the extracted call/return points are
  the paper's `L_call` and `L_ret`;
- `tests/test_calc_pe.ml` — the derived segmentation *is* the paper's
  factorization (the cut labels coincide with the paper's observation and call
  labels, and each segment chain matches its row), the residual tabulates only
  the derived cut points, and the pop count collapses to the per-T-rule scale;
- `tests/test_gen_calc.ml` — the stored code (`lib_gen/generated_calc.ml`) is
  result/table/pop-equal to its in-process reference (`lib/specialize/calc_pe.ml`),
  including at the designated (exact) instance.

The measurement itself re-checks the equality: `bench_paper` compares each
specialized lane's result against the base on every measured program and prints
the relation (`=` on all thirteen).

```
dune test          # all gates
```

**C3 — the performance table (`tab:impl-measure`).**

```
scripts/reproduce-table.sh        # ~5 min on a modern x86-64 core
```

Three process replicates on a pinned core (default core 2, `CORE=n` to
change), each the median of up to 15 samples per cell after two warm-ups;
the printed table is the per-cell median over the replicates, with speedups
and their geometric means. Expected (recorded on an Intel Xeon Silver 4314
under OCaml 4.14.1):

| | summary | denotations |
|---|---|---|
| geometric-mean speedup vs. base | ×1.16 | ×4.06 |
| per-program | faster on all 13 | ×1.17 – ×95 |

Absolute milliseconds are machine-dependent; the speedup ratios and their
ordering are the claim. The worklist-pop counters printed by the bench (and
recorded per TSV row) are machine-independent and should match the recorded
replicates exactly. Those replicates are `docs/data/bench-paper-rep{1,2,3}.tsv`;
aggregate them with

```
dune exec bin/paper_table.exe -- docs/data/bench-paper-rep*.tsv
```

to re-derive the table verbatim. `docs/data/archive-submitted/` holds the older
replicates the submitted paper's table was computed from, and its README says
what changed since.

Building with a flambda compiler (`-O3`) makes every lane about 4–6% faster and
leaves the speedups where they are; it is not worth the extra toolchain
requirement, so the artifact targets a plain OCaml 4.14.1.

**C4 — the specialized analyzer is mechanically generated, not written.**
`lib_gen/generated_calc.ml` is the generated output of the staging program
`staging/calc_stage.ml` (BER MetaOCaml) over the interpreter text; it is
checked in and regenerable byte-identically:

```
scripts/run-gen-calc.sh --check   # needs metaocamlc; prints OK if identical
```

## The measured lanes

| TSV key | paper column | what runs |
|---|---|---|
| `b/s-x` | base | the base abstract interpreter (`lib/analysis/s_abstract.ml`) at the designated instance |
| `gpm/s-x` | specialized, summary | the stored specialized analyzer, analyzed auxiliary summaries |
| `gpm/f-x` | specialized, denotations | the stored specialized analyzer, auxiliary denotations substituted |

All three run at the paper's designated instance (exact environment pinning,
`~exact:true`). Single programs can be run by hand:

```
P="$(grep -v '^ *#' programs/fx2_gcd.t | tr '\n' ' ')"
dune exec bin/main.exe -- interp   "$P" --arg 21     # concrete oracle
dune exec bin/main.exe -- analyze  "$P" --exact      # base (b/s-x)
dune exec bin/main.exe -- run-spec "$P" --aux summary       # gpm/s-x
dune exec bin/main.exe -- run-spec "$P" --aux denotations   # gpm/f-x
```

## The benchmark suite

The table's 13 rows live in `programs/`: ten ports of first-order kernels
(`fx2_*`) plus `sai_fib`, `algo_fact_deep`, `algo_power2`. Their provenance —
the SAI suite (Wei, Chen, Rompf, *Staged Abstract Interpreters*, OOPSLA 2019,
Fig. 9) and classical recursion kernels — and every adaptation are recorded in
`docs/benchmarks.md` and in each file's header.

`programs/fx2_solovay.t` is a fourteenth program, excluded from the table: its
*base* cell alone exceeds the 10 s per-cell budget (one run > 13 s), so no
stable median exists. `scripts/reproduce-table.sh --include-solovay` measures it
anyway (the base cell reports as truncated).

`tests/corpus/` is a different thing — the gate inputs, not benchmarks. The gate
suite sweeps it together with `programs/`, so the specialized-equals-base
equality holds on exactly the programs the table reports, and on 65 more.

## Layout

The construction, in the order the paper builds it:

```text
lib/s/           the source language S — the language an analyzer already exists
                 for: syntax, parser, and the concrete CEK machine
lib/t/           the target language T — the language we want an analyzer for:
                 syntax, parser, the encoding of T entities as S values, and T's
                 concrete machine (the oracle the corpus checks against)
lib/interp_st.ml I_S^T — T's interpreter WRITTEN AS AN S PROGRAM. The centre of
                 the construction: running the S analyzer on it yields the base
                 analyzer for T

lib/domain/      the value domains the analyzer is a functor over: the signature
                 (domain_intf), the tree-grammar domain the measurement uses
                 (domain_rtg), and the disambiguated domain (domain_dis)
lib/analysis/    the generic S abstract interpreter (s_abstract — run on
                 interp_st this IS the base analyzer), and the retargeting that
                 recovers T's machine structure from it (partition, projection,
                 role, role_pe)
lib/specialize/  the SPECIALIZED analyzer (calc_pe): the base analyzer partially
                 evaluated w.r.t. the interpreter text, computed in process

staging/calc_stage.ml       the generator (BER MetaOCaml) that emits the
                            specialized analyzer as code
lib_gen/generated_calc.ml   the STORED specialized analyzer — machine-written,
                            do not edit. This is what the measurement runs
lib_gen/gen_calc.ml         drivers for the stored analyzer

bin/                    main.ml (CLI), bench_paper.ml (the table's harness),
                        paper_table.ml (replicate aggregation),
                        calc_rules.ml (prints the derived rule structure)
programs/               the 14 benchmark programs
tests/                  the gate suite (dune test) and its regression corpus
                        (tests/corpus/)
scripts/                kick-tires.sh, check-programs.sh, reproduce-table.sh,
                        run-gen-calc.sh
docs/                   benchmark provenance and recorded measurement data
outputs/                measurement output (created by the scripts; ignored)
```

## The paper's example

T's expression forms are the paper's — `Int`, `Var`, `Add`, `Sub`, `Mul`, `Let`,
`App`, `Ifz` — plus the extension of appendix E (`Div`, `Mod`, `Lt`, and the
two- and three-argument application forms `App2` / `App3`). So the program the
paper opens with runs directly:

```
dune exec bin/main.exe -- interp   "1 + 2"                    # => 3
dune exec bin/main.exe -- analyze  "1 + 2" --exact            # => {3}
dune exec bin/main.exe -- run-spec "1 + 2" --aux summary      # => {3}
```

`bin/calc_rules.exe` prints the segmentation the specializer derives from the
interpreter text; its rows are the paper's factorization table (`tab:macro`),
`Add1` / `Add2` / `Addr` among them.
