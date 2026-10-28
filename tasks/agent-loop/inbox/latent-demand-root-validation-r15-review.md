# LATENT-DEMAND-ROOT-VALIDATION/r15 — independent pre-run review

Assignment: `/root/latent_demand_root_validation_r15_review`; requested role compiler_referee, Sol/medium; observed model/effort UNKNOWN. Revision 1, STOPPED before Cargo. Read-only; no file writes, Git, checker, build, test, Cargo, Lean, or descendants. Total 300-second reservation was not reset; pre-run stage ended within its 90-second cap. Reviewer CPU/RSS unavailable.

## Verdict: REJECT — BLOCKING input closure gap

R15's workspace snapshot includes all declared workspace members, but it omits eight compile-time inputs referenced by test modules enabled by the exact command's `shadow-apply-candidate` feature (which includes `shadow-f5`). Cargo compiles the test crate before applying the test-name filter, so the focused fixture cannot be reached with these inputs missing.

1. `crates/yu-solver/src/shadow_apply/local_source_observation.rs:1587–1590` has four `include_str!` dependencies absent from the snapshot:
   - `web/playground/examples/yulang2-identity-island.yu`
   - `web/playground/examples/yulang2-ordinary-islands.yu`
   - `web/playground/examples/repeated-choice.yu`
   - `web/playground/examples/polymorphic-escaping-closure.yu`
2. `crates/yu-solver/src/tests/deferred_call_constraints.rs:441–448` has four `include_str!` dependencies absent from the snapshot:
   - `notes/design/2026-10-08-call-source-interface-definition.md`
   - `notes/design/2026-10-07-complete-call-contribution-definition.md`
   - `notes/design/2026-10-08-contextual-function-membership-definition.md`
   - `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md`

All eight files exist in the repository baseline and are absent under the R15 snapshot. Contract requires complete input closure before the one-shot Cargo attempt. Minimum closure is a new admitted, hash-pinned complete snapshot with fresh pre-run acceptance. Do not remove sibling tests, change includes, or weaken expectations.

Authenticated inputs: contract `dc2e1a8a05052a573bff9d5341e2b11a0d937b84d56253e20ee1c07373e8c9ec`; manifest `53464d82524e314e468bb02cf5ed49886a208be9bc2719d1da06ef242685ea32`; candidate `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`; implementation handoff `8f11f94fd31a79aa3879d4b489fd4fe7368299bea4e8bca797ffc48d93b2723a`; source handoff `b79c3ea16b426d4fe2ef07fe1022653c398b820323ba1f903f9e3b3ac4d7a2d8`. All 426 manifest file pins and 10 parent pins matched. All 12 member manifests and 15 path references resolve. Candidate's same-graph demand-root publication had no additional correctness finding in the bounded inspection.

No Cargo attempt occurred. Source adequacy and all parent/production gates remain OPEN. The R15 contract ends on input gaps; this packet is CLOSED_INCOMPLETE and must not be repaired or retried under its existing one-shot grant.
