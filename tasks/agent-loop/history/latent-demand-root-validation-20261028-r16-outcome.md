# R16 outcome: CLOSED_INCOMPLETE

Sprint `LATENT-DEMAND-ROOT-VALIDATION/r16` completed its one authorized Cargo attempt and its independent post-run review. The execution evidence is ACCEPTED; the bounded success goal is not achieved because the sole focused test failed. Per contract, status is CLOSED_INCOMPLETE. No retry, repair, or alternate test is authorized in R16.

## Frozen run

Command:

```text
CARGO_TARGET_DIR=isolated/latent-demand-root-validation-r16/build-target cargo test --manifest-path isolated/latent-demand-root-validation-r16/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

Cargo 1.95.0; rustc 1.95.0. UTC start `2026-10-28T12:42:08.494526+00:00`; end `2026-10-28T12:44:04.869947+00:00`; wall 116.375s; exit 101; no limit termination; CPU affinity `[0]`; peak sampled process-group RSS 1,859,252,224 bytes under the 2 GiB cap. The sampler recorded 570 samples and a final process count of zero. RSS is sampled evidence, not continuous proof between samples.

The focused test compiled and ran. It failed at the test's `emission_cases.first().expect("the ordinary source fixture retains a FreshUse route")` at candidate_scheme.rs:8428. stdout reports one failed test and 816 filtered out. Source stage-2 analysis found all four same-invocation root lookups joined correctly: graphs 3/6, relation 8, root Term index 264, owner index 11; graphs 9/11, relation 150, root Term index 366, owner index 12. `session.execute()` returned `Ok`. The later test-selection path found two call-0 ReplayRows (uses 1 and 3), so its unique-row selection produced no target row. The silent `authenticate_demand_transport` loop then produced no emission case; the failure alone does not identify which individual authentication guard caused this. The rejection stages were not reached. `EvidenceCoverage { gaps: 56 }` remains.

The independent reviewer authenticated all 446 input pins, 16 parent pins, all four exact log hashes and the command/resource record. Verdict: execution evidence ACCEPT; DONE REJECT; CLOSED_INCOMPLETE required. No test/build/Cargo/Lean rerun or other command followed the single attempt.

## Frozen log hashes

Bundle SHA-256: `3db4390a1444cc21be994ff7bdc6ddfcc0f95a80a9e6c353771b72fe1a8d2a2c`.
The argv receipt records the invocation environment and redacts values for credential-like variable names.

- `r16-cargo-1.argv`: `f1fb430738c13ec6799b463b31dc8d13e7caf938e7d6e568bc51a4cb308773e9`
- `r16-cargo-1.resources.json`: `a32c0bf18f50749df61138b1ce4de358b2317dbd6e15a3b089de967c9ba8f9cd`
- `r16-cargo-1.stderr`: `550d76ea80653c335418053cff930fd17d129958f3d14e9d6fc66e2d218f73a6`
- `r16-cargo-1.stdout`: `6e2125980e74d76f180f91a6086ff6ff0b4da0fb04fbd78dd26ed1e7e787b42c`

## Boundaries

The accepted observation is limited to the fixed candidate, fixture and invocation. It establishes same-invocation graph/relation/root/node joins and `session.execute() == Ok` for those observations. It does not establish the intended authenticated rejection path, source/native correspondence, original parent theorem, effect hygiene, principality, termination or production. All remain OPEN. Antecedent evidence gaps remain 56. The earlier native representation result remains bounded and does not close these gates.

The autonomous continuation wording was also clarified in `rules/goal-driven-sprints.md`: an active authorized objective proceeds through its next bounded in-scope step without another confirmation, while existing scope and stop conditions remain binding.
