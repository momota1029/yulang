# R18 outcome — CLOSED_INCOMPLETE

Status: **CLOSED_INCOMPLETE**. The single authorized focused Cargo attempt compiled and ran, then failed because `emission_cases` was empty. No retry or repair was authorized. Independent review accepted the bounded diagnostic observation, not the intended constructor-to-consumer conclusion.

## Frozen inputs and implementation

- Contract: `fedd227744b66af19d5544315130233c4fb666667c996fcafa92dbb8ebf99e9a`.
- Manifest: `d07167958cdb5f93a5370d48568a7a0ab4afc8b8ec31a02ffbdb359848a5b455`; reviewer authenticated 445 unchanged file pins and 32 parent pins.
- Candidate `isolated/latent-demand-transport-classification-r18/crates/yu-solver/src/candidate_scheme.rs`: `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`.
- Implementation handoff `tasks/agent-loop/inbox/latent-demand-transport-classification-r18-impl.md`: `2a81d84ddd55dcabb97ef2c7f91280c35dac83d8c06530a5e9154cd1fc7c9f2b`.
- Independent review `tasks/agent-loop/inbox/latent-demand-transport-classification-r18-review.md` (pre-run and post-run ACCEPT): `d34c0ba0d2edd6afcdaf279183e3a45a69a12e186449de96d4d81ba4dfc9d7ed`.
- Source handoff: `tasks/agent-loop/inbox/latent-demand-transport-classification-r18-source.md`; SHA-256 `9878f83cd1410da9c83305b711bc234b7424617776b46844602ebbd692d8c383`; frozen/stopped at `2026-10-28T13:15:43.696511Z` after ~237 seconds of the original 300-second grant.

The candidate changes only the replay-row loop, adding start identity, both existing skip outcomes, callback count and per-row end summary. The same returned `Option<DemandTransportEvidence>` still feeds `emission_cases`; fixture, guards, authentication call and production behavior are unchanged.

## One-shot execution

Exact command:

```text
CARGO_TARGET_DIR=isolated/latent-demand-transport-classification-r18/build-target cargo test --manifest-path isolated/latent-demand-transport-classification-r18/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

Cargo 1.95.0 / rustc 1.95.0. Start `2026-10-28T13:09:11.082970Z`; end `2026-10-28T13:11:04.850706Z`; elapsed 113.768 s; exit 101; no limit termination. CPU affinity `[0]`; sampled process-group peak RSS 1,890,820,096 bytes (1.761 GiB); sampled process-group peak CPU 44.22 s. The process-resource values are sampled receipts, not continuous independent monitoring.

Frozen log SHA-256:

| Log | SHA-256 |
|---|---|
| `r18-cargo-1.argv` | `6d129811f7c96496371f3d1f17e1ad7890cbe7255f1c5e95a14005b83b49c990` |
| `r18-cargo-1.resources.json` | `0003cf316ccc09e747df3f7c17d9219e4f85ded598dfdaa7b31f6871c8528a1f` |
| `r18-cargo-1.stdout` | `37ba7e01469be1e9f6f00d57256abb9e49dda53bfbeea1e7bf611f684a0ddaf4` |
| `r18-cargo-1.stderr` | `ec10657838ff7912bb520a621eee1994be6d413d2e2ce7d234d209e122c6f27c` |

One focused test ran; 816 filtered; 0 passed / 1 failed. `session.execute` returned `Ok`, but `emission_cases.first()` was empty and the test panicked at `candidate_scheme.rs:8479`. No `DemandTransportEvidence` was accepted; subsequent raw-transformer mutation/restoration assertions did not run.

## Bounded row observations

All four replay rows had one start and one end record, no pre-call skips, two callbacks, and `returned_evidence=false`:

| Call/use | Child/lower/upper | Root index | Owner / route | Observed callbacks |
|---|---|---:|---|---|
| 0/1 | 61/58/35 | 299 | Module / 0 | `MatchingRoute` → `Rejected("positive-function-node-absent")` |
| 0/3 | 119/116/93 | 338 | Module / 2 | `MatchingRoute` → `Rejected("positive-function-node-absent")` |
| 3/5 | 191/188/168 | 393 | Local / 0 | `MatchingRoute` → `Rejected("positive-function-node-absent")` |
| 3/7 | 248/245/225 | 430 | Local / 1 | `MatchingRoute` → `Rejected("positive-function-node-absent")` |

`positive-function-node-absent` records failure to select exactly one same-route positive Function. The observation cannot distinguish zero matching nodes from duplicates. Each rejection returns from the whole authentication call; later routes were unvisited, not exhausted. Source handoff maps rows 0–1 to Call occurrence 2 (`f 1` in `invoke`) and rows 2–3 to Call occurrence 22 (`h z` in `local`). Each execution passed the listed capture/import/FreshUse/physical/replay-ancestry guards before failing unique same-route positive selection. This finite mapping establishes no general adequacy or compiler defect.

## Review, gates and integration

Fresh pre-run review ACCEPTed the one-loop candidate. Post-run review ACCEPTed only the bounded retained observation, independently checked all four row identities/events and the failed assertion, and required `CLOSED_INCOMPLETE`. The primary's first post-run resume message transposed two characters in the stdout hash; the reviewer stopped, Luna corrected the pin, and the actual unchanged bytes were authenticated before review continued. No rerun occurred.

Preserve `EvidenceCoverage { gaps: 56 }`. `YulangClosure.SourceProblem.InferenceSoundness`, Call/shared-witness, Generalize allocation, source/native correspondence, effect hygiene, principality, termination, and production remain **OPEN**. No source theorem or parent gate closes here.
