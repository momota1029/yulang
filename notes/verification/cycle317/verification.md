# C317 verification

- Lean 4.35.0. `lake build --wfail` for the 35 exact added
  [modules](modules.txt) completed at 3,044 jobs, exit 0.
  [Build output](build.txt). Not a whole-repository build.
- The 35 exact source files also ran individually under
  `lake env lean --trust=0 -DwarningAsError=true`, all exit 0.
  [Source statuses](source.txt).
- Six standalone audit parts import only `Yulang.*`. All ran
  independently under `--trust=0` with warnings as errors.
  [Statuses](audit-status.txt).
  [Exact statements](Cycle317ExactStatements.txt) separately check the
  counterexample plus repaired regression, projection equivalence, the
  current full frame certificate, whole occurrence vs owner, and old/new
  endpoint lookup and reuse from installed rows.
  [1](Cycle317Surface1.txt) · [2](Cycle317Surface2.txt) ·
  [3](Cycle317Surface3.txt) · [4](Cycle317Surface4.txt) ·
  [5](Cycle317Surface5.txt) print the dependency sets of all 194 added
  public theorems; only `propext`, `Classical.choice` and `Quot.sound`
  occur. [Summary](surface-summary.txt).
- The supervisor-owned axiom checker body ran unchanged with scoped
  imports for these 35 modules, exit 0 (94,283 declarations checked). [Scoped gate](scoped-gate.txt).
  This is not a claim that all `Yulang` or `SpecExamples` ran.
- `bash tools/verify-lean.sh . 3407f8f99 --no-build`, exit 0; that is the
  local proof tree at the published C316 base
  `32376552c732c7743b310211f5c46a00aa9045e8`. `git diff --check` also
  passes. The 35 new barrel imports exactly match the new modules.
  No existing Lean module or frozen config was changed.
  Full diff-check output in parts:
  [00](diff-00.txt) · [01](diff-01.txt) · [02](diff-02.txt) ·
  [03](diff-03.txt) · [04](diff-04.txt) · [05](diff-05.txt) ·
  [06](diff-06.txt) · [07](diff-07.txt) · [08](diff-08.txt) ·
  [09](diff-09.txt).
- No Rust, CI, Yulang2 runtime, concrete Sat, or whole Lean build.
  The changed compiler and its downstream transaction are isolated Lean
  work, not an enabled production policy or a changed language rule.
