# Cycle 299 verification

This directory contains exact theorem signatures, independent trust-0 output,
full static verification logs, Lean commands and five executable fixtures.
`verify-focused.sh` compiles the new library import tail using a prior
Lean 4.35.0 cache, not a full Lake build. The old rigid executable runs
inside Lean; no Rust or Yulang2 oracle was rerun. A successful table read
alone is not source evidence. The actual mixed evidence appears only in
the C277 reached post-install state. The actual depth-two rigid result is
a different elaborator; synthetic disconnected-cycle/missing/repeat controls
are not source executions.
The three-slot nested V8 fixture is a genuine initial state with calculated
preliminary packet emissions; the command performs no raw install. Its
two-install interface requires both operational installation proofs.

- `focused-verification.txt`: isolated build and audits, including old regressions.
- `direct-verification.txt`: direct Lake-environment audit replay and fixture receipts.
- `static/diff-*.txt`: concatenate in lexicographic order for both complete
  `tools/verify-lean.sh --no-build` logs, including exact integration-tree checks.
- `source-sha256.txt`: every added compiled or executable Lean input and the barrel.
