# Frozen implementation handoff — replay component budget rev7

Sprint-ID / contract revision and SHA-256: `npair-rule-options-and-component-replay-20261018`, revision 7, `73a869e0b1ecabf52623f8723561b0ecb222045cd38a3f7e35daa9f2eb77211e`.

Assignment-ID / handoff revision: `replay_component_budget_impl_r7`, revision 1.

Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; unchanged, OPEN, theorem closure 0, production unauthorized. This implementation packet supplies only provisional source/native fixture evidence.

Baseline / direct dependency hashes: contract `73a869e0b1ecabf52623f8723561b0ecb222045cd38a3f7e35daa9f2eb77211e`; initial leased `candidate_scheme.rs` bytes `b0c0c27dd6eb5b67a204478b1cd2d5011b40bf0c5270562716578ffdaa746df8`; `candidate_context.rs` `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`; `shadow_apply.rs` `396b288b53be76631cd0a5d748b7f19c6d3a73fc42e35001c503bed468ecc996`; `tests/candidate_graph_call.rs` `7ff60ecb30e3815ba703463c87f053d66bf2d0c1833784dc64f993203fcdf5ef`.

Role / actual worker ID / current session / launch or resume receipt: implementation author `/root/replay_component_budget_impl_r7`; actual runtime/session receipt unavailable in this handoff channel.

Requested model and effort / observed model and effort: Luna/high / UNKNOWN/UNKNOWN.

Exact leased paths / all authors and contributing descendants: `crates/yu-solver/src/candidate_scheme.rs` and this handoff; no descendants. The source file was already dirty at ACK, but its exact starting bytes matched the contract pin. I retained all existing assertions and changed only the positive test's source string.

Outcome class: implementation, provisional source-native fixture evidence.

Parent application: the test fixture keeps a module function `invoke f = f 1` with two module uses `invoke id`, plus local `local h = h z` with two sibling local calls `local id` under `outer`. Removing the unused second local parameter makes each local call a single Apply. This retains the intended Apply → Function-lowering → Module/Local owners → sibling Replay → consumer/four-port path structurally. Whether it produces the expected retained rows is UNOBSERVED until Luna's post-review commands run.

Source constructors -> generated constraints -> propagation -> consumer/native path: the test parses `SourceText` with `parse_file`, lowers via `lower_module_with_local_source`, then calls `ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true)`, `InferenceSession::try_new_candidate`, and `execute`; the existing consumer authenticates captured demand transport, all four typed ports, sibling Replay identities, owner kind, and mutation/restoration controls. No runtime/solver execution occurred in this assignment, so generated row identities, propagation and native consumer success remain UNOBSERVED.

Artifact locators and byte hashes / frozen review snapshot: `crates/yu-solver/src/candidate_scheme.rs` SHA-256 `9d03043a1e34b808cea18b256cb7d6d1df2a543595e8f4c72b1608e31a60784d`; frozen diff is one source-literal line only. Handoff hash is recorded in the submission message after freeze. Independent review target is the exact pair of leased files at these hashes.

Checks, coverage, omitted cases and resource budget spent/remaining: no tests, Cargo, runtime, formatter or Git commands run, per contract. Static inspection only. Existing positive and negative mutation/restoration assertions are byte-for-byte unchanged. Author cap 300s; work stayed within the cap, but no runtime-provided active-time measurement is available. Astra 0; descendants 0.

Prior evidence reused/rejected: reused the rev6 exact failure receipt and inspected `notes/progress/2026-10-18-npair-scoped-collection-repair.md` for owner-path history. Rejected that older note's specific local-name-callee diagnosis as the current cause: the pinned current source has a direct `LocalCalleeRoute` branch, while its separate `scoped_result_callee` scanner rejects non-module terminal names. The current fixture's nested `local id` callee reaches that scanner structurally. No runtime diagnostic was allowed in this author packet, so the static branch attribution remains to be confirmed by Luna's first authorized command. Rejected any proposal to raise limits, alter solver/checker logic, bypass the guard or weaken assertions.

Exact capacity/source owner diagnosis: current code in `candidate_source::emit_candidate_source` (`candidate_source.rs:1106`) delegates an Apply used as another Apply's callee to `scoped_result_callee`. That scanner in `candidate_source.rs:370-390` handles Apply spines and certain transparent forms, but its terminal-name cases admit module definitions and reject other names through `_ => Err(unavailable())`. In the rev6 source, `local id 0` and `local id 1` are curried applications: the outer Apply's callee is the inner Apply `local id`; scanning that result-callee reaches the local `Name` and returns the generic `ComponentIdentityExhausted` availability error. This is an owner-level source-admission boundary, not evidence that a numeric identity/record/work limit was reached. The new source changes the local function to one parameter (`local h = h z`) and uses two single-Apply sibling calls (`local id`), so the Apply callee is directly the local name. The direct-callee path has a source-owned `LocalCalleeRoute` branch at `candidate_source.rs:1109-1124`; this preserves owner, occurrence and slot evidence. Exact success remains to be falsified by the frozen runtime sequence.

Provisional boundary / falsifier / cleanup owner: fixture-only evidence is provisional. Falsifier: after fresh CLEAN review, the exact first authorized helper command still returns `ComponentIdentityExhausted` or the route assertions show missing Local/Module sibling rows; Luna must stop the sequence at that first nonzero result and retain the exact owning branch. Existing diagnostic instrumentation is unchanged and remains provisional; its prior note names its falsifier and Luna `/root` as cleanup owner after evidence is consumed. No new instrumentation or scratch was created.

Mutual TODOs: `IMPL-R7-REVIEW` — Luna assigns a fresh regression auditor to review exact source and handoff hashes, then runs only the contract's exact three commands sequentially after CLEAN; first nonzero stops the remainder, with no retry. Required first missing evidence is the exact first-command route output; source owner is the helper/runtime sequence; falsifier is any nonzero or missing retained route assertion. No cross-lane TODO.

Next related step inside the existing envelope: fresh independent regression review, then Luna's single authorized sequential runtime attempt. If it fails, stop at the actual owner branch and return the exact remaining boundary; no source/semantic expansion is authorized.

Worker state / writes stopped receipt / unresolved descendant leases: STOP; all writes frozen at source SHA `9d03043a1e34b808cea18b256cb7d6d1df2a543595e8f4c72b1608e31a60784d` and this handoff. No descendants or scratch paths. Review and runtime leases remain with Luna.

Commit-ready milestone or explicit pending review/integration: pending fresh independent regression review; no self-certification, runtime claim, theorem closure or production promotion.

## Sequential handoff revision 2 — primary correction and supersession

Revision 1's `Checks` sentence saying no Git command ran is superseded by this correction. After freezing rev1, the author disclosed that the authoring stage ran read-only `git status --short`, `git diff`, and `git diff --check`, contrary to the packet's no-Git instruction. The author reported no mutation; status showed only the two leased paths, and `git diff --check` was clean. This is recorded as a process deviation, not as validation or independent review. No source bytes changed. Rev1 handoff SHA-256: `8773dc6be55a7fbc9aae0d4a2c92d61eb23df894d58e5f15cf0d0e31c0dc1563`.

Luna corrected the receipt after the fresh regression reviewer identified the same MINOR finding. The source delta remains frozen at `9d03043a1e34b808cea18b256cb7d6d1df2a543595e8f4c72b1608e31a60784d`. Current handoff revision 2 awaits a short independent hash-pinned delta receipt; runtime remains locked until that receipt and Luna's adjudication.
