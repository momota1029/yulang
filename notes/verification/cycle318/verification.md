# C318 verification

- Lean 4.35.0. Focused `lake build --wfail` targeted exactly the 36 new
  [modules](modules.txt); dependency build finished at 3,080 jobs, exit 0.
  [Build](build.txt). No whole-repository build.
- All 36 exact added sources ran individually under
  `lake env lean --trust=0 -DwarningAsError=true`, each exit 0.
  [Source exit codes](source.txt).
- Eight standalone audit files import only `Yulang.*`. Each ran separately
  with the same trust and warning flags. [Exit codes](audit-status.txt).
  [Exact statements](Cycle318ExactStatements.txt) check the actual isolated
  install and generation, the same-owner mixed descriptor, both heads and
  four rows in one nonvacuous model, the shadowed-read interval, and actual
  recovery of a generating-row receipt from a physical slot.
  [Early](Cycle318Early.txt), [layout](Cycle318LayoutContract.txt),
  [1](Cycle318Surface1.txt), [2](Cycle318Surface2.txt),
  [3](Cycle318Surface3.txt), [4](Cycle318Surface4.txt), and
  [5](Cycle318Surface5.txt) print 136 distinct theorem axiom sets.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur;
  see [summary](surface-summary.txt).
- The supervisor-owned checker body ran unchanged on the 36-module
  import set, separately from the standalone declarations: 94,715 checked, exit 0.
  [Scoped gate](scoped-gate.txt). This is not a global Yulang/SpecExamples audit.
- `bash tools/verify-lean.sh . 8e01a8f07 --no-build` and
  `git diff --check 8e01a8f07` pass. The base maps to the verified handoff
  on `work/dots-main` `ac6c3f215a4ffaee155bd9612285b4f1471209d2`.
  The 36 added imports match the 36 new modules exactly, all appended to
  the barrel. No frozen config or existing Lean module was altered.
  Complete diff output:
  [00](diff-00.txt) · [01](diff-01.txt) · [02](diff-02.txt) ·
  [03](diff-03.txt) · [04](diff-04.txt) · [05](diff-05.txt) ·
  [06](diff-06.txt) · [07](diff-07.txt) · [08](diff-08.txt) ·
  [09](diff-09.txt).
- Rust, CI, concrete Sat, Yulang2 runtime and whole Lean build were not
  run. Neither production compiler behavior nor language semantics was changed.
