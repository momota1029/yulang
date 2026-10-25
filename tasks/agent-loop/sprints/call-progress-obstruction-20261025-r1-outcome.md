# LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r2 outcome

Status: **FAILED_VERIFICATION / UNACCEPTED**, failure stage `LAUNCHER`.
Baseline contract: `call-progress-obstruction-20261025-r2.md`, SHA-256
`01aa44596c1f2aeae77afb0c90f5026fc263e522b7771c2ced274deb957f9e9c`.
Governing proposition contract: r1, SHA-256
`6020b57d97d0642be5702dafe52efa5fc302165ded16d5e717a159b7e92bee5c`.

## Frozen candidates

P submitted a candidate construction of a typed `CallTerm` and an actual
five-step prefix ending at the View-wrapped Force head:

- Source `CallViewedForceReachability.lean`, SHA-256
  `ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c`.
- Handoff `20261025-call-viewed-force-reachability.md`, SHA-256
  `2f91698e60fa4d45d7128bd6ce270fc45211a319adb68a63aaa77b7e09c2e8e7`.

Q submitted the arbitrary-state no-successor candidate. Static constructor
inversion covers all 28 current `CallControlStep` constructors:

- Source `CallViewedForceStuck.lean`, SHA-256
  `71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9`.
- Handoff `20261025-call-viewed-force-stuck.md`, SHA-256
  `bf85d3499e4f0e159c96756cb7ffc55c5101aeb69c287da6c43bc96f58d69744`.

These are **uncompiled candidates**, not Lean-certified theorems. Both authors
stopped with all writes ceased; no descendants or scratch files remain. P/Q
source/dependency pins matched. Neither candidate has received independent
review. No `.olean` or `.ilean` outputs were generated.

## Failure and resource accounting

P attempted a wrapper using `python - <<'PY'` to call
`lake env lean -j1 -M1024 ...`. The shell returned exit 127 because `python`
was unavailable. **`lake`, Lean, and the theorem source were never launched.**
This is a launcher failure, not a Lean proof failure or compiler verdict. Q's
Lean invocation, Luna composition, signature/axiom query and independent review
were not run. No reviewer was appointed.

The r2 contract required stopping at the first failure, so no retry or repair
occurred within r2. P's exact active elapsed time and the authors' model/effort
observations are UNKNOWN; charge the complete P 900-second and Q 300-second
grants. The 1,500-second composition/verification/review/integration envelope
was unused. A fresh verification-only revision is required; it may reuse only
these frozen candidates and the already pinned dependencies.

## Scope boundary

No theorem is accepted. The parent progress, Call A/B, source/native, inference
A/B and production obligations remain OPEN. The formal View-wrapped Force
shape remains only a candidate obstruction until both proofs compile, compose
with accepted finite-prefix typing, and pass fresh independent review. The
three UNKNOWN quarantines and unrelated untracked Force evidence were preserved.
