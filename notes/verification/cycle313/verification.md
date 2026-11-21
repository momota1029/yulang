# C313 verification

- Scoped Lake: from `lean/`, select exactly the 29 new modules from
  `git diff --name-only --relative 25445a2d8 -- Yulang`, translate their
  paths to module names and run `lake build --wfail <those modules>`.
  Exit 0; Lake reports **1,630 jobs** including dependencies (warm cache).
  This did not build all unrelated targets.
- For each of the same 29 source files, run
  `lake env lean --trust=0 -DwarningAsError=true Yulang/<name>.lean`.
  29/29 exit 0. See [source-trust0.txt](source-trust0.txt).
- For each of the 11 new `Audit/Cycle313*.lean` files independently, run
  `lake env lean --trust=0 -DwarningAsError=true <audit file>`.
  11/11 exit 0. The Audit files import only Yulang modules, never one another.
  The independent surface audits cover 250 explicit declarations.
  The combined logs display 416 axiom-list lines (including repeated audits)
  and 17 lines reporting no axioms, for 433 checks total. Only
  `propext`, `Classical.choice` and `Quot.sound` appear. Full output:
  `axioms-00.txt` through `axioms-05.txt`.
- Diff only: `bash tools/verify-lean.sh <checkout> 25445a2d8 --no-build`.
  Exit 0 after committing the audit files, which the script requires.
  Full output `diff-00.txt` through `diff-11.txt`; checkout path shortened
  in the first line. Earlier pre-commit draft check failed solely because the
  audit files had not been added yet. `git diff --check` passed.
- Verified all 29 additions present exactly once in the barrel, append-only.
  No older proof, toolchain, acceptance rule, or specification changed.
  Full Lean, Rust, CI and the supervisor-owned axiom gate were not run.
