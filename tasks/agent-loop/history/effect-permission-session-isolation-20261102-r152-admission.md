# R152 admission — session-owned permission binding

Admitted under the ongoing user request to analyze and push Rust work when it
is safe. R151 remains open on activation/state association; R152 handles a
separate concrete cross-session permission-join risk in the already-dirty
research diff.

Contract: `tasks/agent-loop/sprints/effect-permission-session-isolation-r152.md`,
SHA-256 `5fd4a9441a90be2b1201b179d8afb83c71ca2bbf4a8ca25c6f78e4da0d5bcc51`.
Committed source baseline `225c5519943fc490c3d5620683918674f4f6afd5`.
Frozen input patch:
`tasks/agent-loop/inbox/effect-permission-session-isolation-r152-input.patch`,
SHA-256 `643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a`.
The copied patch was generated from HEAD `6ef549d344851e39ada0f631a2926919f301543c`;
all three Rust base blobs match the pinned `225c551` blobs byte for byte.

The independent read-only audit is summarized at
`tasks/agent-loop/history/unpushed-rust-solver-diff-20261102-audit.md`, SHA
`89459ef4639a93f3db7a936ba8ca4b49fe83dd48debf30d7a9612f425588f37c`.
Its exact target diff hash matches the frozen patch. It found a major risk:
`candidate_scheme.rs` accepts route/store/effect-state/registration references
that can come from different sessions, while checking only equal source IDs and
session-local ordinals. `candidate_receiver.rs` has a separate deletion of
owner/batch/live-state, provider/arm and permission-origin checks and is excluded.
Runtime files remain UNKNOWN_WRITER/QUARANTINED.

Proof lane: 600 seconds; implementation lane: 900; fresh referee: 360; primary
integration: 180; total ceiling 2040 seconds. Candidate changes remain
unapplied and uncompiled. No tests/builds/Lean, cache, scratch, environment,
checkout, worktree, or path-lease release. Only a complete reviewed candidate
can be checkpointed as research; production remains unauthorized.
