# The benchmark suite

Where each of the fourteen programs in `programs/` comes from, what was adapted
to express it in the target language T, and what was left out of the reported
table. Every program's own header repeats the essentials; this file is the
overview and the rationale.

T is a first-order language: integers; `+`, `-`, `*`, `/`, `%`, `<`; `ifz`;
`let`; and functions of one, two or three arguments. No data structures, no
state, no higher-order functions. The suite therefore draws on benchmarks that
are first-order or honestly first-order-izable, and every adaptation is recorded.

Each program's `# case: arg=N => V` lines are its concrete oracle — the
input/output pairs it must reproduce. `scripts/check-programs.sh` runs all of
them through the S-coded interpreter `I_S^T`.

## Where they come from

**Ported from prior work.** Ten programs come from Fig. 9 of Wei, Chen, Rompf,
*Staged Abstract Interpreters* (OOPSLA 2019) — the closest related work, and the
reason to use its suite rather than invent one.

| program | origin | what had to change |
|---|---|---|
| `sai_fib` | fib | none; already first-order and single-argument |
| `fx2_church` | church | Church-numeral equality defunctionalized to iteration counts; the composition-of-closures content is not first-order-expressible |
| `fx2_fermat` | fermat | tested number pinned to n = 15; the random draws become a deterministic seed orbit `s ↦ (s+3) mod 16` |
| `fx2_rsa` | rsa | scaled instance p=3, q=11, n=33, e=7 ≠ d=3; extended-gcd replaced by the equivalent first-order search for d (Bézout coefficients go negative) |
| `fx2_mbrotz` | mbrotZ | the escape iteration with max-count 8 is an unrolled `s0..s8` chain; the grid runs from 0 (2-D complex arithmetic with negatives is out of budget) |
| `fx2_lattice` | lattice | the 4-value lattice algebra, including the original's dead lexicographic comparator; mutation dropped (T is pure) |
| `fx2_solovay` | solovay-strassen | the full pipeline (modpow, two-variable Jacobi with the reciprocity flip, Fermat stage, Euler check, outer generate loop); n = 15 pin and seed orbit as in fermat |
| `fx2_gcd` | (gcd) | Euclid by remainder; the second operand is fixed at 3 |
| `fx2_collatz` | (collatz) | none beyond the T syntax |
| `fx2_tak`, `fx2_ackermann`, `fx2_mccarthy91` | see below | |

**Classical kernels.** The rest are staples of the partial-evaluation and
program-analysis literature, natively first-order:

| program | origin |
|---|---|
| `fx2_ackermann` | Ackermann's function (a standard partial-evaluation example, Jones–Gomard–Sestoft); measured at A(2, ·) |
| `fx2_tak` | Takeuchi's tak, from the Gabriel Lisp benchmark suite; `main` takes one argument, so it computes tak(x, 2, 0) |
| `fx2_mccarthy91` | McCarthy's 91 function (Manna & McCarthy 1970) |
| `algo_fact_deep` | factorial — a deep call/return spine |
| `algo_power2` | 2^n by recursion — the classical Ershov/Futamura power example, base fixed at 2 |

## What is measured, and what is not

The table's thirteen rows are every program above except `fx2_solovay`.

`fx2_solovay` is excluded because its *base* cell alone exceeds the 10 s
per-cell budget (one run > 13 s), so no stable median exists for it. It is kept
in the suite, and `scripts/reproduce-table.sh --include-solovay` measures it
anyway, reporting the base cell as truncated. Nothing else is excluded.

Instance sizes are chosen so the concrete oracle terminates within its fuel and
the analysis terminates within the per-cell budget; the choice is recorded in
each program's header (`fermat`'s n = 15, `rsa`'s n = 33, `tak`'s fixed y and z,
`mbrotz`'s max-count 8). These are scaling decisions, not semantic ones: each
program computes the function its origin computes.

## Reading the numbers

Two columns of the bench output are worth more than the times.

**`steps`** is the worklist pop count. It is machine-independent: the same
program analyzed by the same analyzer pops the same number of times on any
machine. It is the check that a re-run analyzed what the recorded run analyzed.

**`rel`** compares each specialized lane's result against the base's, per
program. It is `=` where they agree — which, with the analyzed auxiliary
operators, is every program.

## The regression corpus

`tests/corpus/` is a separate thing: 32 `.s` and 65 `.t` programs, mostly small
shapes, that exist to cross-check the interpreters and the analyzers against each
other. They are gate inputs, not benchmarks, and none of them is reported. The
gate suite sweeps them together with the fourteen programs above, so the
equality it establishes — the specialized analyzer computes what the base
computes — holds on exactly the programs the table measures, and on a good deal
more.
