# LATENT-DEMAND-ROOT-VALIDATION/r15 outcome — 2026-10-28

Status: **CLOSED_INCOMPLETE**. R15 ended at mandatory pre-run review; Cargo was not run.

## Exact result

Fresh independent reviewer `/root/latent_demand_root_validation_r15_review` rejected pre-run input closure. The exact feature set compiles sibling `cfg(test)` modules before Cargo filters the requested test name. Eight `include_str!` inputs are absent from the R15 snapshot: four playground sources referenced by `shadow_apply/local_source_observation.rs:1587–1590`, and four design documents referenced by `tests/deferred_call_constraints.rs:441–448`. All eight exist in the baseline repository. Therefore the focused test could not be reached reliably from the frozen snapshot. Review handoff: `tasks/agent-loop/inbox/latent-demand-root-validation-r15-review.md`.

The reviewer authenticated all 426 manifest entries and 10 parent pins, the contract, candidate and producer handoffs; all 12 workspace member manifests and 15 direct path dependencies resolve. That workspace closure did not include these compile-time Rust inputs. The reviewer found no additional bounded defect in the unchanged same-graph root publication. No Cargo, build, test, metadata, Lean, or Git operation occurred in the review.

The exact missing inputs are:

- `web/playground/examples/yulang2-identity-island.yu`
- `web/playground/examples/yulang2-ordinary-islands.yu`
- `web/playground/examples/repeated-choice.yu`
- `web/playground/examples/polymorphic-escaping-closure.yu`
- `notes/design/2026-10-08-call-source-interface-definition.md`
- `notes/design/2026-10-07-complete-call-contribution-definition.md`
- `notes/design/2026-10-08-contextual-function-membership-definition.md`
- `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md`

Contract: SHA-256 `dc2e1a8a05052a573bff9d5341e2b11a0d937b84d56253e20ee1c07373e8c9ec`. Manifest: `53464d82524e314e468bb02cf5ed49886a208be9bc2719d1da06ef242685ea32`. Candidate: `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`. Implementation handoff: `8f11f94fd31a79aa3879d4b489fd4fe7368299bea4e8bca797ffc48d93b2723a`. Source handoff: `b79c3ea16b426d4fe2ef07fe1022653c398b820323ba1f903f9e3b3ac4d7a2d8`.

R15 contract says any input gap ends the packet. No snapshot repair or retry is made under R15. A fresh sprint may admit the exact missing compile-time inputs and require fresh independent pre-run acceptance before any new Cargo grant.

Original `YulangClosure.SourceProblem.InferenceSoundness`, source Call/shared-witness, Generalize allocation, complete source/native correspondence, effect hygiene, principality, termination, and production remain **OPEN**. The 56 antecedent evidence gaps remain the prior observation; no R15 execution refined them.
