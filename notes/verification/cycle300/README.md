# Cycle 300 verification

The fixed three-slot ground V8 source has a verified raw execution, two
actual guarded installs, a settled same-model dictionary, and an exact
three-phase machine for **only** the given initial state and root.
Commands in this directory compute raw edge data, candidate data or the
finite ranked reader. The independent Lean theorems validate the raw
transitions, exhaust the other successors in this fixture and prove when
the dictionary is evidenced. The CLI does not implement the generic
kernel or execute Rust.

- theorem-index.md: exact statements corresponding to all standalone
  audit commands; audit outputs appear here.
- focused-verification.txt: isolated import-tail build under Lean 4.35.0
  against a prior cache. Includes old audits, no whole Lake build or CI.
- direct-verification.txt: direct Lake-environment replay and input hashes.
- static/diff-*.txt: both full verify-lean.sh --no-build outputs,
  in lexicographic chunk order, against the previous work and exact
  integration trees.
- source-sha256.txt: every new Lean file, runnable fixture and the barrel.
