# C316 verification

- Lean 4.35.0. `lake build --wfail` selected exactly the 32 added modules
  listed in [modules.txt](modules.txt); 3,008 dependency jobs, exit 0.
  [Build](build.txt). No whole-repository Lake build.
- Every exact added source was also checked independently with
  `lake env lean --trust=0 -DwarningAsError=true`; 32/32 exit 0.
  [Source status](source.txt).
- Five standalone audit files import only Yulang modules. Each ran with
  `--trust=0` and warnings as errors. 251 explicit printed declaration
  checks (one axiom-free); only `propext`, `Classical.choice` and
  `Quot.sound` occur.
  [1](Cycle316Surface1.txt) · [2](Cycle316Surface2.txt) ·
  [3](Cycle316Surface3.txt) · [4](Cycle316Surface4.txt) ·
  [exact statements](Cycle316ExactStatements.txt).
  The exact audit separately checks genuine child generation, same-model
  leaf evidence, the recursive refutation, the failed bridge, and the
  exact bad row in the stable frame.
- The supervisor axiom checker body ran unchanged with scoped imports
  for these 32 modules, exit 0; 93,842 non-system declarations examined.
  [Scoped gate](scoped-gate.txt). Not the whole repository/SpecExamples.
- `bash tools/verify-lean.sh . 28d4c7958 --no-build`, exit 0 (the local
  Lean base corresponding to published C315
  `5e22ff4b1aed2868798b9a340174051ad40ddcca`), and `git diff --check`.
  32 new barrel imports exactly match the 32 module paths; no frozen
  files or existing Lean modules were altered. Full diff output in parts:
  [00](diff-00.txt) · [01](diff-01.txt) · [02](diff-02.txt) · [03](diff-03.txt) · [04](diff-04.txt) · [05](diff-05.txt) · [06](diff-06.txt) · [07](diff-07.txt) · [08](diff-08.txt) · [09](diff-09.txt).
- No Rust run, CI run, whole Lean build, compiler integration of the
  experimental endpoint allocator or language acceptance change.
