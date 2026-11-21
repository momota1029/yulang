# C315 verification

- Repository Lean toolchain 4.35.0. Focused Lake build selected the 23 new
  modules in [modules.txt](modules.txt) and their transitive dependencies,
  with --wfail; exit 0 (2978 dependency jobs). [Build log](build.txt).
  The whole repository Lean barrel was not built.
- All 23 exact Lean source files were checked independently with --trust=0
  and warningAsError=true; exit 0 for each. [Source log](source.txt).
- Four standalone audit files import only built Yulang modules, not other
  audit files. All passed with --trust=0 and warnings as errors. 168
  explicit declaration checks: eight axiom-free, and no axiom beyond
  propext, Classical.choice and Quot.sound.
  [1](Cycle315Surface1.txt) · [2](Cycle315Surface2.txt) ·
  [3](Cycle315Surface3.txt) · [4](Cycle315Surface4.txt).
- Independent kernel environment scan of 93,413 non-system declarations
  in the same scope passed. The supervisor axiom checker body was copied
  unchanged; only the import list of temporary audit was scoped.
  [Scoped gate](scoped-gate.txt). No full repository / SpecExamples audit.
- The append-only diff gate exited 0 against the verified C314 Lean
  base (published b923bc0dad34b3b69e69b0a49f80e5e4230ec100, equivalent
  local Lean base 9b0e3c752). All 23 module imports were appended to
  lean/Yulang.lean with their corresponding new module. No deleted Lean
  line or change to the frozen files. Diff output split without dropping
  checks; absolute working directory omitted from the first line:
  [00](diff-00.txt) · [01](diff-01.txt) · [02](diff-02.txt) ·
  [03](diff-03.txt) · [04](diff-04.txt) · [05](diff-05.txt) ·
  [06](diff-06.txt) · [07](diff-07.txt) · [08](diff-08.txt) ·
  [09](diff-09.txt) · [10](diff-10.txt) · [11](diff-11.txt) ·
  [12 / exit](diff-12.txt).
- No Rust, CI, full Lake build, changes to language acceptance, or retrofit
  of the experimental allocator into source execution.
