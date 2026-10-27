# NAME-ENTRY-TARGETED-CAUSALITY-20261028/r1 — primary outcome

Disposition: **INCOMPLETE overall; bounded direct, Condition and BlockExpression observations accepted. Actual Sequence-frame coverage remains OPEN.** The fresh reviewer found one MAJOR evidence/coverage issue: the source handoff calls the `{x; z}` case an equivalent Sequence case, while the executable trace proves that it returned through `BlockExpression`, not `Sequence`. This outcome narrows the accepted evidence to what the retained trace shows; the frozen source handoff is not rewritten. No token-causality defect was found in the reviewed instrumentation.

## Receipts

- Contract SHA-256: `8e9fd3c3c07a7771537e68265db5587ec63520516c2170e086688c51da3b7cd3`; baseline `yulang3` / `36a4867038a7d44e866e841c6194cf6223b98960`.
- Source handoff: `tasks/agent-loop/inbox/name-entry-targeted-causality-20261028-source.md`, SHA-256 `8a3f77de88fcd42c7ad2494fed84ae9947528a4a0d10ee827525f22a9e8fd172`.
- Frozen candidate `machine.rs`: SHA-256 `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d`.
- Frozen driver `name_entry_trace.rs`: SHA-256 `1bdc20af3157a8df34d93a2872607e282927eb9ab851c3d505b135d6f5c1598e`.
- Retained trace `source/name-entry-trace.txt`: SHA-256 `ff8a8d88e29533f2d207206f492f7ed811ce9d705692ede5e99f5d388080b51c`.
- Unchanged `receiving.rs`, `runtime/mod.rs`, and `OriginalNameEntryTrace.lean` match the five admitted hashes in the contract.

Source ACK/start `2026-10-27 16:05:18 UTC`; source cessation ACK `16:10:27 UTC` (309 seconds, within 400). All five baseline hashes matched before edits. Exactly one locked Cargo run started `16:09:44 UTC`, exited 0, tool wall 3.850 seconds; one build job. CPU/RSS UNKNOWN; 1 GiB was a target. Tests=0; Lean/Lake=0; no retry/fallback. `git diff --check` exited 0. The fresh reviewer `/root/name_targeted_causality_review` ACKed at `16:11:02 UTC` and completed at `16:11:59 UTC`; elapsed 57 seconds of 180. Reviewer was read-only and ran Git/Cargo/tests/Lean=0.

## Accepted runtime observations

- Direct positive case: exactly one target attempt, invocation 1 / entry parameter 1; receipt 0 from source parameter 0 and Name site 8 accepted. Value/view 2; cells before bind 2, bound cell 2, after bind 3.
- Condition stale-Local case: supported syntax and path executed. Parameter `x` at site 12 / receipt 1 returned through `Condition`. Local `z` at site 13 / receipt 2 returned directly to the actual target ValueEntry. Both observations carry value/view 2 and cell count 3. The unique target attempt has no token and binds fresh cell 3.
- `{x; z}` stale-Local case: the Parameter→Local `z` value/view/cell comparison and target no-token record are present, but the immediate return frame is `BlockExpression`. Accept this only as BlockExpression evidence. It does not execute the distinct `Frame::Sequence` path; Sequence remains UNRESOLVED.

The target attempt is recorded inside ordinary ValueEntry handling after the fresh bind and is independent of the sticky historical correspondence trace. The fixed driver query requires exactly one actual entry-parameter-1 attempt. The reviewer confirmed that observation vectors do not control execution and found no new behavior-changing branch or receipt construction.

## Scope and next boundary

The MAJOR finding is about the source handoff's overclaim and the missing actual Sequence path, not an observed stale token acceptance. The frozen source handoff retains its original wording for provenance; this adjudicated outcome explicitly supersedes that wording for accepted conclusions. No separate Sequence-specific repair or rerun is authorized by this sprint.

This closes no semantic seed, native readback, ReturnAlignment, original theorem, parent/A-B, complete Call, effect hygiene, principality, termination or production gate. The conditional Lean packet remains frozen; no new Lean work occurred. All source leases are frozen pending a separately admitted sprint.
