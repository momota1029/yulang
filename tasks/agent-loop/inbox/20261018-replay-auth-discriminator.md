# Frozen implementation handoff — Replay authentication discriminator rev8

Sprint-ID / contract revision and SHA-256: `npair-replay-auth-discriminator-and-same-c-interpretation-20261018`, rev2, `2cf068bb099903c3f96c3a1a0a7eccb3525eb54d5de776bc1e9110f2bdadd9d4`.

Assignment-ID / handoff revision: `replay_auth_discriminator`, revision 2. Luna primary appended the reviewed macro-scope repair; revision 1 is preserved by its known SHA in current-state review history.

Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; unchanged original quantifiers, source domain, accepted semantics and fixed `c`; parent OPEN, closure 0, production unauthorized.

Baseline / direct dependency hashes: `candidate_scheme.rs` before edit `9d03043a1e34b808cea18b256cb7d6d1df2a543595e8f4c72b1608e31a60784d`; `candidate_context.rs` `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`; sprint contract `639da02aacadb88726954b7bcec652ad6f86596e7c22666d5b69fc60fb0de4f7`. All rechecked before freeze; `candidate_context.rs` remains byte-identical.

Role / actual worker ID / current session / launch or resume receipt: `/root/rev8_replay_auth_diagnostic`, current session. Luna acknowledged the exact contract, leases and pins before authoring. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. No descendants.

Exact leased paths / all authors and contributing descendants: `crates/yu-solver/src/candidate_scheme.rs` and this handoff; author `/root/rev8_replay_auth_diagnostic`, no descendants. No runtime artifacts or scratch paths created.

Outcome class: implementation, provisional test-only diagnostic instrumentation.

Parent application: no parent condition discharged; closure remains 0. The existing source-to-candidate-constraint-to-propagation-to-native-consumer path and its authentication decisions remain as before. The test now has a causal trace point for the exact failing Replay row, route owner/index identity, and first rejected authentication predicate, so Luna's authorized post-review command can identify whether the failure is row attribution, retained route ownership, or a later authentication stage.

Source constructors -> generated constraints -> propagation -> consumer/native path: the existing fixture still parses and lowers the same module/local Apply source, collects scoped candidate constraints, executes the candidate session, enumerates every `ReplayDemandRow`, and calls the same authentication logic. The diagnostic observer reports `ReplayDemandRow` and matching `FreshRouteOwner` plus route index, followed by the first rejected predicate or acceptance. The production-facing `Option<DemandTransportEvidence>` wrapper calls the same internal routine with a no-op observer. Existing fixture rows, Module/Local sibling assertions, wrong-use/root/Replay mutation controls, route mutations, physical-slot mutations, and acceptance/rejection branches were not filtered or weakened. No compiler command ran here, so source-to-execution success and runtime output remain UNOBSERVED. Fresh review revision 1 found a BLOCKING Rust macro hygiene issue: `rejected!` was defined before its `route_owner` and `route_index` bindings.

Artifact locators and byte hashes / frozen review snapshot:
- `crates/yu-solver/src/candidate_scheme.rs`: `ebbfa6da533a6c90df9b34075c397ebe5dbf9a9bac991e6f853138c5df1f71ab`
- `crates/yu-solver/src/candidate_context.rs`: `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`
- This handoff hash to be supplied with frozen submission.

Checks, coverage, omitted cases and resource budget spent/remaining: no tests, Cargo, runtime, formatter or Git command run, per stage 2. The targeted test adds diagnostic output immediately before its existing success expectation. All existing assertions remain in place. Author cap 600s; exact observed active-time accounting is unavailable in this worker channel. Runtime envelope 480s remains reserved to Luna after independent CLEAN review. Astra 0; descendants 0.

Prior evidence reused/rejected: reused the rev7 closeout `tasks/agent-loop/sprints/npair-rule-options-and-component-replay-20261018-closeout.md` and failed runtime meta `tasks/agent-loop/runtime/20261018-replay-component-budget.helpers.meta.json`: rev7 failed at `.expect(None)` after 3.695s; the old source did not expose the exact row or first rejected predicate, and no retry is authorized. Reused the prior Replay ancestry/FreshUse owner trace in `tasks/agent-loop/inbox/20261018-replay-ancestry-impl.md` and the `demand-transport-impl` handoff as evidence for the existing relation/map/consumer path, not as proof of this fixture's retained row. Rejected any source-domain, semantic, checker, solver, coverage or assertion change; no runtime cause is claimed before the new diagnostic command.

Provisional boundary / falsifier / cleanup owner: observer is diagnostic only and provisional. Falsifier: the unchanged targeted command still fails without an exact row, matching route identity, and first rejected predicate; instrumentation changes which authentication cases accept/reject; required Module/Local siblings or mutation controls disappear. Luna owns cleanup after evidence is consumed. No source/native theorem or production promotion follows from this instrumentation or later green tests.

Mutual TODOs: `REPLAY-AUTH-DIAG-REVIEW` — Luna assigns a fresh compiler_referee to review the frozen source/handoff hashes, compare every prior acceptance/rejection branch and mutation control, and check diagnostic fidelity/noninterference. After CLEAN review and Luna ACK only, Luna runs the one exact targeted command under the 480s sequential envelope and records the output. Required evidence: exact row plus matching route identities plus first rejected predicate. Falsifier is any omitted sibling/control or changed authentication result. No proof-lane TODO is asserted by this implementation packet.

Next related step inside the existing envelope: stop for independent review of these frozen bytes. After Luna ACK and CLEAN review, primary runs only the authorized targeted diagnostic command. If it identifies a fixture/retention defect, repair only that demonstrated cause under the existing leases and freeze for fresh review before the helpers/graph/example commands. No test/runtime has been run by this author.

Worker state / writes stopped receipt / unresolved descendant leases: STOPPED writing at the source and handoff hashes above; no descendants, generated outputs or scratch paths. Luna owns runtime leases and all later commands.

Commit-ready milestone or explicit pending review/integration: revision 1 review was BLOCKING on macro scope. Luna moved the macro definition inside the route loop, after both route identity bindings, without changing predicates or observer content. The corrected bytes are frozen pending a fresh independent compiler_referee review; no tests/runtime, parent closure or production authorization.


## Sequential revision 2 repair receipt

Independent review 1: BLOCKING at `candidate_scheme.rs` because a `macro_rules!` definition referenced loop-local `route_owner` and `route_index` before those bindings were in scope. Luna repaired this by placing the macro definition inside the loop, immediately after the route tuple binding. The observer remains identical and each previous rejection branch still returns `None`; no predicate or fixture assertion was changed.

Source SHA-256: `ebbfa6da533a6c90df9b34075c397ebe5dbf9a9bac991e6f853138c5df1f71ab`. Context SHA-256 remains `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`. The primary has not run tests, formatting or runtime; fresh independent review of the corrected frozen bytes is required before the targeted diagnostic command.
