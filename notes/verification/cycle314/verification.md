# C314 verification

- Toolchain: repository Lean 4.35.0. Only the 32 new Yulang modules in
  [modules.txt](modules.txt), with their dependencies, were selected for
  Lake. The repository's complete barrel was not built.
- Focused Lake build with --wfail exited 0 (1557 jobs in the dependency
  graph): [build log](build.txt). Each of the 32 exact source files was
  also separately checked with --trust=0 and warningAsError=true, exit 0:
  [source log](source.txt).
- The six new independent audit files import production modules and do
  not supply proofs or modify the built barrel. Each was checked at
  --trust=0 with warnings as errors. There are 189 explicit public
  declaration checks, of which four are axiom-free; the only axioms used
  by the others are propext, Classical.choice, and Quot.sound.
  [1](Cycle314Surface1.txt) · [2](Cycle314Surface2.txt) ·
  [3](Cycle314Surface3.txt) · [4](Cycle314Surface4.txt) ·
  [5](Cycle314Surface5.txt) · [6](Cycle314Surface6.txt).
- Separate kernel environment scan: the supervisor axiom checker body
  was copied unchanged into a temporary file and only its imports were
  scoped to the same 32 additions. It checked 69,356 non-system
  declarations transitively, exit 0: [scoped gate](scoped-gate.txt).
  This is not a whole-barrel or SpecExamples gate run.
- Existing Lean files are append-only for the cycle. All 32 modules
  were added to lean/Yulang.lean in the applicable source publication.
  tools/verify-lean.sh with --no-build verified the entire C314 diff
  against its Lean base (C313 exact published pin
  81ed8a6aba89ada711c8c091013feeba76b94491 and equivalent local Lean
  base 9b633c338). The log is split without removing checks, except
  that the first line's absolute working-directory name is omitted:
  [00](diff-00.txt) · [01](diff-01.txt) · [02](diff-02.txt) ·
  [03](diff-03.txt) · [04](diff-04.txt) · [05](diff-05.txt) ·
  [06](diff-06.txt) · [07](diff-07.txt) · [08](diff-08.txt) ·
  [09](diff-09.txt) · [10](diff-10.txt) · [11](diff-11.txt) ·
  [12 / exit](diff-12.txt).
- No Rust, CI, full Lake, or all-repository audit is claimed. No changes
  to the language specification, compiler executable, or Rust files.
