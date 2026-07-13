# docs/

Documentation and recorded measurement data. Start from the repository-root
`README.md`.

- **[benchmarks.md](benchmarks.md)** — the benchmark suite: where each of the
  fourteen programs comes from, what was adapted to express it in T, and why
  `solovay` is not in the reported table.
- **[data/](data/)** — the recorded replicates. `bench-paper-rep{1,2,3}.tsv` are
  the runs the table is computed from; aggregate them with
  `dune exec bin/paper_table.exe -- docs/data/bench-paper-rep*.tsv`.
  `archive-submitted/` holds the older replicates the submitted version of the
  paper's table was computed from, and a note on what changed since.
