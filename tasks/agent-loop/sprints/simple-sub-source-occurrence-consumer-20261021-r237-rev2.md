# Sprint R237 — Resolve accepted source route to canonical-child consumption

Status: ACTIVE_SOURCE_AUDIT; Luna sole primary. No subagents.
Baseline: `480b9c4cb` (`research/simple-sub-intrusion`). Revision 2 supersedes R237 rev1 only by adding one bounded test-only source probe and its exact file lease; original parent, source domain, resource cap and stop conditions are unchanged.
Authority: unchanged Simple-sub/computation-forwarding parent, approved occurrence qualification, contextual residual-lineage policy, R71/R72.

## Outcome and evidence

R71/R72 and the original theorem retain their complete quantifiers and accepted source domain. R236 established the production attach-site census and the control-flow possibility that a typed drain consumes a canonicalized child before dispatch enters level-based extrusion. R218/R221/R229 supply an accepted higher-order callback WorkBound case but no alias of its slot-4 item. R237 seeks an accepted source/action history with third-owner physical slot, equality alias, canonical-child consumption, then raw-key WorkBound copy; otherwise identify the first missing source constructor/consumer edge. A finite negative source case does not refute the universal claim.

Success evidence is a source-authentic chain from Yulang2 input through HIR/source Actions, produced rows and occurrence-qualified equality, physical slot/readback, typed-drain Transport/Context/Dispatch, selected raw slot, exact fibers/witnesses and resulting consumer context. Preserve all original identities, dependencies, residuals, rollback/retry and scheduling premises. Tests and manual graph states do not prove the parent theorem.

## Method and exact leases

Read only the relevant constructors/consumers in `candidate_source.rs`, `candidate_scheme.rs`, `candidate_extrusion.rs`, `candidate_intrusion.rs`, `candidate_context.rs`, `candidate_effect.rs`, `shadow_apply.rs`, `lib.rs`, plus exact R71/R72 and occurrence/residual authority.

One inert `#[cfg(test)]` source probe may be added to `crates/yu-solver/src/shadow_apply/local_source_observation.rs`, using the existing ordinary CandidateInference and R148 trace/forest records. Begin from the R221 higher-order-loop source with `repeat loop x` inside the recursive `loop` body (or another statically justified one-edit candidate). The probe may report actual parsing/lowering, solver acceptance, row-merge/parent-write order, WorkBound raw keys, and relation transport/consumer events. It must not change production code, source semantics, expected output, or existing tests. Keep the probe only if it yields a useful accepted route or reusable falsifier; remove it before freezing if the candidate has neither the alias-changing merge nor the target raw copy.

Test command, if needed, is limited to the exact new test name under `cargo test -p yu-solver --features shadow-apply-candidate --lib <test-name> -- --nocapture`, with a 120-second timeout. No package-wide tests/builds or source execution beyond that test. All test output is candidate evidence, never theorem closure.

Write leases:
- `tasks/agent-loop/sprints/simple-sub-source-occurrence-consumer-20261021-r237-rev2.md`
- `notes/theory/2026-10-21-r237-source-occurrence-consumer-route.md`
- `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (one test-only probe only)
- `tasks/agent-loop/current.json` (Luna synchronization)

All other code is read-only. No new syntax, fixtures in playground, implementation, semantic change, expected-output change or test outside the exact leased file.

## Falsifier and boundaries

A source candidate is falsified for this packet if it is rejected by an authentic constructor, lacks the third-owner alias, never consumes the canonical child before the selected WorkBound, or the WorkBound raw lookup lacks the relevant source lineage. A positive trace must include all these joins and distinguish the canonical child’s key.context replay use from relation-local post-check transport. A source-qualified consumer requiring a distinct unavailable lineage is a counterexample candidate for Luna adjudication, not production authority.

No production slice is approved. R71/R72, Simple-sub A/B, semantic approval, independent review, full solver suite and production remain OPEN. The R237 900-second solo envelope is unchanged from rev1; revise only within its remaining budget, no carryover. No agents are active or launched. Elapsed time is UNKNOWN if not directly observable; stop at the envelope. Run `python3 tools/agent_sprint.py check`, `git diff --check`, pin changed inputs, commit/push exact leased paths, and leave a clean tree.
