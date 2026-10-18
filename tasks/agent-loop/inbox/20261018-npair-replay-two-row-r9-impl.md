# r9 two-row Replay implementation handoff

Sprint-ID / contract revision and SHA-256: `npair-original-witness-and-replay-diagnosis-20261018-r9`, revision 9, `749ffee49ba3c196244653c239d035c8d2245913f287db25de1df306655500ed`.

Assignment-ID / handoff revision: `r9-two-row-implementation`, revision 1.

Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN/closure 0; unchanged original fixed-c theorem, quantifiers, source domain, R/W/Z cases, `rho_u`, F1/FK1 and consumer obligations. Native work is the bounded per-row diagnostic in the exact test named below and is provisional evidence only.

Baseline / direct dependency hashes:

- `crates/yu-solver/src/candidate_scheme.rs` intake: `25ce531aa10d5f2ab85f363248f6d7ff0c062b93c70389e3d25f4a1b67e608bb`; frozen output: `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`.
- `crates/yu-solver/src/candidate_context.rs`: `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` (read-only).
- `crates/yu-solver/src/shadow_apply.rs`: `eb0b9dcd8529e067ec8778c7888f3595ad8df466e1be4243b1d2104c853952d7` (read-only).
- r8 failure receipt: `tasks/agent-loop/runtime/20261018-replay-constructor-r8.meta.json`, `51cc528eebef6243f9968288c2688c18b4305a945566c431d9f0bcf61aed11e9`; prior r8 implementation handoff `d927e9ade81585c6ec832e69a19075eec52ef843cc24fe3c7c41039125b2aa40`.
- r8 contract: `529fe913b9cf2645399a7e8ce135b5535bc26fc7d0336e5dbf27ef582e64f8e9`; FCW8 artifact `d81fbe9969a10328dd8a9f65bfff6c0598767b770deb57f0b8244c3e2b2735e5`; paired proof handoff `a672deb54c27ff9e57cc14ebfc414ca9c842df9b23c0ce2327e28a186ac6d2bb`.

Role / actual worker ID / current session / launch or resume receipt: `implementer`; `/root/npair_replay_two_row_r9_impl`; `current-session`; current-session launch recorded in Luna-owned `tasks/agent-loop/current.json`.

Requested model and effort / observed model and effort: Luna/high / UNKNOWN/UNKNOWN.

Exact leased paths / authors: only the named function `replay_constructor_lineage_observes_rejected_cross_route_authentication` in `crates/yu-solver/src/candidate_scheme.rs` and this handoff. Sole author; no descendants.

Outcome class: provisional source/native instrumentation.

Parent application: before the pre-existing assertion block, the function now iterates the complete `ReplayDemandRow` vector and emits one indexed diagnostic per row. Each record includes the full row, its call's native identity, keyed Module route/use identity matching the demand root, child/lower/upper lineage, lower-input relations, lower producer admissions with emissions/readback, and observed FunctionPort edges whose parent is that row's Replay child. This makes both call-0 records observable even when the existing unique-row selection yields no `target_row`. It preserves the exact source fixture and existing selected-row diagnostics. This static change does not explain the actual row values or pass the test; runtime remains pending independent CLEAN review and Luna's one authorized exact run.

Source constructors -> generated constraints -> propagation -> consumer/native path: the fixed fixture still parses and lowers through `ConstraintBatch::collect_candidate_mode_scoped`, executes candidate inference, reads `ReplayDemandRow`s from the retained context, and uses the existing native call table and observed Replay/FunctionPort/provenance records. The new diagnostics report these observations before assertions; no constructor, propagation, authentication or execution behavior was changed. No Cargo, build, test or runtime command was run by this worker.

Artifact locators and byte hashes / frozen review snapshot: `crates/yu-solver/src/candidate_scheme.rs` SHA-256 `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`; frozen with this handoff. The existing fixture and every existing assertion, including expected `target_rows.len() == 1`, remain textually unchanged within the leased function. No independent review has occurred on this r9 delta.

Checks, coverage, omitted cases and resource budget spent/remaining: intake pin hashes match; read-only inspection confirms `ReplayDemandRow` carries call, child, lower, upper, complete lower/upper BoundKeys, demand and match flags; r8 metadata records a single exact invocation ending at the existing assertion with two call-0 rows, exit 101, and truncated merged output. No tests/builds/runtime were run in r9 implementation. Covered diagnostically: every Replay row present at runtime, with per-row call/source-use/producer/consumer records. Not covered until runtime: actual printed contents, whether route matching supplies every source/use association, and successful completion past the unchanged assertion. Assignment cap 360s; conservatively charge full 360s because exact active duration was not measured; 0s remaining. Sprint budget is Luna-owned. No scratch outputs.

Next related step inside the existing envelope: fresh independent `compiler_referee` review of this exact source snapshot. If CLEAN, Luna may perform the single exact runtime invocation with complete stdout/stderr capture under the frozen contract. Any compiler/assertion failure ends that runtime grant; do not retry or alter expectations.

Mutual TODOs: Luna review/runtime request `r9-two-row-implementation` — first missing evidence is independent CLEAN review followed by the one exact output capture; source owner is this named test in `candidate_scheme.rs`; required inputs are the frozen contract and source/dependency hashes above; outputs are Luna-leased r9 stdout/stderr/meta paths; falsifier is a source/dependency pin mismatch, review blocker, compile failure or unchanged assertion failure. This handoff grants no write authority to those outputs.

Worker state / writes stopped receipt / unresolved descendant leases: STOPPED; source and handoff frozen, no descendants, no scratch files, no runtime outputs. Exact writes stopped after the two leased paths were frozen.

Commit-ready milestone or explicit pending review/integration: pending fresh independent compiler review and Luna's exact runtime; no theorem closure, production authority, source/native success claim, self-certification or Git action.
