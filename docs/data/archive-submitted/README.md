# The replicates behind the submitted paper's table

These are the measurements the submitted version of `tab:impl-measure` was
computed from (geometric means ×1.19 / ×3.93). They are kept for provenance
only; they no longer describe this code.

Two subsequent fixes changed the measured artifact:

- **The widening schedule.** The base analyzer widened at every revisited table
  key. The paper's appendix says widening is applied at the reentrant points --
  the eval-calls and returns -- which is what the specialized analyzer retains as
  its chain boundaries. The base now derives those points from the analyzed
  program (`S_abstract.reentrant_points`) and widens only there, so base and
  specialized widen at the same places and reach the same result.

- **The language.** The interpreter had no `Add` arm, and no `+` or `==` in S:
  addition was spelled `a - (0 - b)` and the key comparisons `iszero(k - k')`.
  The paper's listing has all three. They are restored, and the benchmark ports
  use `+` rather than the workaround -- which is what the paper measures.

The current replicates are `docs/data/bench-paper-rep{1,2,3}.tsv`
(×1.16 / ×4.06). The worklist-pop counters, which are machine-independent, are
unchanged by the first fix and drop under the second exactly as the smaller
programs predict.
