# LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r3 — verification continuation

Status: **READY; no authors active**. Baseline: `2ed4a20a6` on
`research/simple-sub-intrusion`. This is a fresh verification-only revision
after r2 stopped at launcher failure. It does not carry r2 budget. P and Q
candidate sources remain frozen and uncompiled; no author restart or source
repair is authorized.

## Frozen claim and inputs

Preserve the exact propositions and scope from:

- r1 proposition contract: `call-progress-obstruction-20261025-r1.md`, SHA-256
  `6020b57d97d0642be5702dafe52efa5fc302165ded16d5e717a159b7e92bee5c`.
- r2 exact output leases: `call-progress-obstruction-20261025-r2.md`, SHA-256
  `01aa44596c1f2aeae77afb0c90f5026fc263e522b7771c2ced274deb957f9e9c`.
- r2 outcome: SHA-256
  `dc329ddc99486ff2ae375b6f398721cbcabacde7ea9de67c9f8f7398a67e0176`.

Frozen author candidates:

| Artifact | SHA-256 |
|---|---|
| `CallViewedForceReachability.lean` | `ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c` |
| P handoff | `2f91698e60fa4d45d7128bd6ce270fc45211a319adb68a63aaa77b7e09c2e8e7` |
| `CallViewedForceStuck.lean` | `71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9` |
| Q handoff | `bf85d3499e4f0e159c96756cb7ffc55c5101aeb69c287da6c43bc96f58d69744` |
| accepted finite-typing outcome | `f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d` |

Revalidate the relevant source and compiled dependency hashes from r1/r2 before
the first invocation. In particular P imports `ControlTyping` and `Contracts`,
Q imports `ControlSyntax`, and composition imports `CallFiniteTyping`, P and Q.
The accepted `initial_call_prefix_terminal_typing` theorem is the only typing
preservation premise used in composition.

## Luna proof application

Create `reachable_typed_viewed_force_stuck` using frozen
`viewed_force_prefix` / `viewedForceTarget`, Q's
`viewed_force_no_successor`, and
`initial_call_prefix_terminal_typing`. Given
`hsuffix : FramesTyped sig suffix (.original (.base .unit)) result`, prove the
five-step target is `CallStateTyped sig target result`, retains exactly
`.active (.force (.view (.delay (.ret (.original .unit))) occurrence))`, and
has no `CallControlStep` successor. Preserve the outer suffix result index and
do not conflate it with `Original.Ty target.resultType`.

No Rust/source producer, frontend realization, native correspondence, Call
A/B, inference A/B, semantic approval or production claim follows. The formal
obstruction is accepted only if P, Q and composition compile, the query confirms
the exact signatures and allowed axioms, and a fresh nonauthor review is CLEAN.

## Exact Luna output leases

- `notes/theory/lean/YulangClosure/CallProgressObstruction.lean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallProgressObstruction.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallProgressObstruction.ilean`
- `notes/theory/lean/.lake/call-progress-obstruction-r3-check.lean`
- `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r3-verification.jsonl`
- `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r3-review.md`
- `tasks/agent-loop/sprints/call-progress-obstruction-20261025-r3-outcome.md`

Luna also owns the previously enumerated P/Q `.olean` and `.ilean` output pairs
from r2. The P/Q source and handoff files are FROZEN and excluded from r3 write
leases. No other source, scratch, generated or untracked Force path is leased.

## Resources, invocation protocol and stop condition

Fresh r3 cap: **1,500 seconds**: Luna composition 240, serialized verification
480, fresh independent review 600, integration 180. No r2 budget carries
forward. Astra 0; no author children. Four Lean invocations maximum and in this
strict order: P, Q, composition, exact signature/axiom query. Each uses one
process/CPU, 1 GiB and a 120-second timeout. Use direct `lake env lean` commands
or a wrapper launched explicitly with `python3`; never invoke `python`.

For each module, pass the exact leased `.olean` and `.ilean` paths with `-o`
and `-i`, capture complete stdout/stderr, exit and timeout status, timestamps,
source/output hashes, and flush its JSONL receipt row before the next
invocation. Revalidate dependencies before running; reject stale unreceipted
outputs. Stop at the first pin mismatch, proposition mismatch, elaboration
failure, timeout or missing output. No automatic retry or source repair.

After all four invocations pass, appoint a fresh nonauthor `compiler_referee`
to review the complete frozen packet. Integrate only after CLEAN review and
Luna adjudication. Preserve all three UNKNOWN quarantines. Luna alone owns
state, review, explicit-path Git integration and push.
