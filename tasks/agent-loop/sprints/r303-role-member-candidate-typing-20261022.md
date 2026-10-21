# Sprint R303 — source-backed role member typing in the unchanged Types sample

Status: RUNNING, solo Luna primary; independent review unavailable under the user's no-subagent instruction.
Branch / baseline: `research/simple-sub-intrusion` / `6afa11887`.
Authority: continuing user goal and R149; `notes/design/2026-10-20-r149-types-console.md`; unified design §§4.3–4.5, 5.1, 6, 9–10; proof companion §§3.1–3.6, 4.5, 7.1–7.5; R302 checkpoint.
Contract revision 1 / SHA-256 recorded in `current.json`; primary approval: user-goal solo continuation.

## Original outcome and success evidence

Parent remains the exact unchanged 142-byte Types and 92-byte Console samples, original pinned Yulang2 library closure, source-owned imports, public types, ordered whole-module execution/output, and applicable source/native proof. This sprint does not narrow that parent or its source domain.

Immediate goal: make the original `Display.a.say` role member and the unique ordered-pair `Display.show` implementation member available to candidate inference under their original source identities, and type the selected original method body in the same inference session after receiver constraints settle. Advance unchanged Types beyond `DeferredSelectionUnavailable`; preserve the captured role prerequisite and FieldTail receiver/result Value+Effect rows. Any successful path must be driven by settled receiver constraints and authenticated source identities, not names alone, raw target text alone, or trial typing.

Success evidence: source member identity resolves to exactly one unrecovered original body; candidate constraints for that body retain source-node correspondence and same-session receiver/role prerequisites; candidate selection occurs only after receiver lower bounds settle and rejects zero/multiple matches; focused unchanged-Types solver/CLI evidence advances to actual method-body checking or execution. A focused structural/source-root falsifier must show that same-spelled members from another role or implementation cannot cross-route. Test evidence is implementation evidence, not a source/native theorem.

Before: R302 verifies FieldTail source identity and Capture/FreshUse transport, observes an ordered `(int, str)` receiver bound with ordered Int/Str child lowers, and counts one ordered-pair target among 14 authenticated Display implementations. No implementation is selected and no role/implementation body is consumed. Types fails at deferred selection; Console at imported-name preflight.

Open premises: authentic source member body formation and HIR/candidate ownership; implementation target matching to settled receiver bounds; role prerequisite discharge; selected member body inference; console providers/operation selection; complete module execution; source/native correspondence; independent review. No semantic or source restriction is authorized.

## Two continuing lanes

Proof: Luna follows original `SourceRoleMemberId` / `SourceImplementationMemberId` and `SourceNodeKey` through any new source-root or body-formation path, checks recovery, uniqueness, owner/module identity and the source constructor-to-candidate-constraint correspondence, then applies each verified bridge to R149. No local lemma closes R149.
Implementation: Luna extends the HIR sidecar and candidate path so original role/implementation member bodies enter inference without fabricated top-level bindings. Preserve the exact source-owned prerequisites and FieldTail row bundle; select from settled bounds; then continue the unchanged Types path as far as the established runtime permits.
Fresh review is unavailable because the user explicitly forbids subagents. Record all evidence as solo/unreviewed.

## Exact leases and resources

Exact leases: `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/source_identity.rs`, `crates/yu-hir/src/module/source_role.rs`, `crates/yu-hir/src/module/source_impl.rs`, `crates/yu-hir/src/module/local_source.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-hir/src/module/source_exports.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_call.rs`, `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/shadow_apply.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/pinned_stdlib.rs`, `tools/inference-playground/tests/cli_yulang2_samples.rs`, this contract, `notes/theory/2026-10-22-r303-role-member-candidate-typing.md`, and Luna-owned `tasks/agent-loop/current.json`. No wildcard leases.

Solo serial work, 3600-second cap, no carryover, one Cargo/build/test process at a time, no background work. No subagents. Unknown legacy workers remain UNKNOWN and their leases untouched. Current work has a fresh active-session primary receipt; missing runtime model metadata remains UNKNOWN. Stop at goal, genuine source/semantic obstacle, no-progress bound, cap, user STOP or session end. Commit and non-forced push coherent verified checkpoints. The next sprint boundary is required before changing exact leases or semantics.

## Integration, proof and remaining parent

Only Luna changes current state and Git. Proof, source/native, implementation, independent-review and production gates remain distinct. FieldTail and Capture/FreshUse evidence is reusable but not retroactively a proof of method typing. R149 remains OPEN until both unchanged samples execute with exact output and the original source/native/A-B obligations and required review close. Console remains active parent work after the Types dependency advances.
