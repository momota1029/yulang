# Research artifact reconciliation after R50

Primary-only worktree reconciliation on `research/simple-sub-intrusion`, after
R50 closeout. The current active Simple-sub parent remains unchanged and
**OPEN, 0 -> 0**. This is repository preservation work; it adopts no semantics
and changes no compiler or evaluator behavior.

## Tracked test-only worktree changes

Before restoring the two tracked files, Luna archived their exact diff at
`notes/progress/2026-10-19-unreviewed-test-only-worktree-delta.patch`, SHA-256
`5e3280b99998e1e513a408bdb360104843b6a1a79edda60a1289133facc4d332`, with the
source and baseline hashes recorded in the companion archive note. The delta
contains only tests in `shadow_apply.rs` and
`candidate_local_self_recursion.rs`. The recursive fixture overlaps the
R36/R37 candidate whose pre-execution reviews blocked it; the ordinary-call
assertion had no matching frozen assignment in the audited records. Both
remain unreviewed candidate code in the archived patch and are not applied.
Only those two tracked files were restored to `HEAD`; both now hash-match the
committed baseline.

## Historical research files

The individually named untracked R35–R41 and R48 design, proof, handoff,
review, closeout and candidate-patch artifacts were inspected and are now
archived as research records. Their own status labels remain authoritative:
blocked candidates remain blocked, proposal-only designs remain unadopted, and
open source/proof premises remain open. R22's frozen suffix-provenance handoff
is preserved as historical evidence. The R4 Replay source correspondence
draft and its draft handoff remain explicitly **DRAFT / NOT FROZEN / NOT
REVIEWED**; version control records these bytes but does not make them an
active assignment or a proof result. `current.json` remains the only live
scheduling state.

The only generated cache found was
`tools/__pycache__/agent_sprint.cpython-312.pyc`; it was removed as disposable
Python bytecode. No tests, build, Cargo command, runtime probe, or compiler
verification ran. `python3 tools/agent_sprint.py check` passed after repairing
the duplicated current-state worker/lease inventory; that is static state
evidence only.

All prior worker identities are terminal. The primary is WAITING for the
user's decision on the reviewed R50 proposal. The archival commits do not
authorize a new research sprint, semantic decision or implementation lease.
