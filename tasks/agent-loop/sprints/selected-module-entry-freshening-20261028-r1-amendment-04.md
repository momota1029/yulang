# Amendment 04 — restore protected publication trace prefix

Parent: `SELECTED-MODULE-ENTRY-AND-FRESHENING/r1`. This amendment adds one bounded candidate repair following the independent REJECT at `tasks/agent-loop/inbox/selected-module-entry-freshening-amendment01-review.md` (SHA-256 `676b54b6848a33219a3dff09749c682805d6f3cf3722f4eff0d347adb5771e30`) and selector recommendation `/root/r3_selector`. It incorporates the corrected source pin from amendment 03 (SHA-256 `6c155dd154d1cd106ad41b2484f870570e63d61f0b0ff2cf2f4643ffd27261e9`).

## Exact repair lease

Reopen only `isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/src/candidate_scheme.rs`, whose pre-edit SHA-256 is `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`. Restore the baseline publication event prefix `negative-root-publish term=... node=...` verbatim so the protected original assertion in `candidate_effect.rs` remains unchanged and passes its prefix contract. If capture identity is retained in the event, append it after the baseline fields. Make no other source or expectation changes.

Only additional writable path: `tasks/agent-loop/inbox/selected-module-freshening-prefix-repair.md`. No Git operations, build, Cargo, tests, Lean, shared-root source edits, runtime-path access or additional paths. Report final `candidate_scheme.rs` SHA, exact diff, handoff SHA, writes-stopped status and any deviation. Freeze both outputs after at most 150 seconds; no automatic renewal. The worker may not edit a prior frozen snapshot or any sibling file. Primary remains sole integrator.

## Review, admission and remaining resources

The three-file research candidate remains REJECTED. This repair does not admit a baseline, authorize Rust verification or close a proof, source/native, H_u, A/B, effect-hygiene or production gate. After writer stop, a fresh nonauthor `compiler_referee` must authenticate all three final owners and review the complete delta against `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`, including the previously uninspected `shadow_apply.rs`, exact baseline prefix/assertion, all Graph literals, constructor-absent trace paths and unchanged non-test behavior. Review cap: 300 seconds, read-only, no execution. Primary may admit the research baseline only after PASS.

Remaining sprint envelope: 1,400 seconds, already charged prior work stays charged. This amendment allocates at most 150 seconds repair, 300 seconds review, 650 seconds primary-owned exact verification/integration after PASS and admission, and 300 seconds contingency. Preserve the existing two-attempt / shared 180-second Cargo ceiling, one job, 2 GiB RSS and at least 4 GiB available memory. Before any Cargo invocation, freeze exact test names/argv, feature flag, inputs, resource receipt and output paths; execute no broad `formal_permission` filter that may sweep unresolved probes. No retry or budget reset is implied.

The source/native reconstruction blocker and H_u AUTHORITY_BLOCKED status remain unchanged. UNKNOWN writers and quarantined paths remain untouched.
