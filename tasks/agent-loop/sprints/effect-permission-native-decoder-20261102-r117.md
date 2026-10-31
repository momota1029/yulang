# EFFECT-PERMISSION-NATIVE-DECODER/20261102-R117

Status: admitted continuation of the active Rust/Lean soundness and effect-hygiene goal after R116 closeout. Preserve source semantics, original quantifiers and parent gates.

## Fixed outcome

Create a concrete Rust patch candidate for the existing private projection that authenticates the selected provider operation member against the same formal annotation's retained permission. Reuse `SourceInternalProjection` and `ProviderNativeContextProjection::capture`; check same formal registration/owner, source Lambda/occurrence, selected Catch arm/provider operation identity and native endpoint. The result must be consumed when assembling the existing projection. It must not be a disconnected accessor/metadata record or a new inference/suppression rule. Any observer failure remains local to the optional projection and must not affect ordinary solving.

Deliver the exact patch as `tasks/agent-loop/artifacts/effect-permission-native-decoder-r117.patch` and a source handoff at `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-rust.md`. Do not apply it to the dirty source tree. The patch is a **research candidate**, not integrated Rust implementation. Identify all field/symbol/configuration dependencies, exact baseline, hunks, invariants, failure behavior, and a counterexample each check rejects. If the available owner projection cannot authenticate the join, freeze a smaller non-promotable patch candidate or `NO_SAFE_CODE_SLICE`; do not fabricate IDs or weaken source checks.

## Immutable source and proof pins

Rust baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`:

- `crates/yu-solver/src/candidate_receiver.rs`: `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` (patch base and only patch target).
- `crates/yu-solver/src/candidate_effect.rs`: `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`.
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- `crates/yu-solver/src/lib.rs`: `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.
- R116 selected-member Lean candidate: `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`.
- R116 source handoff: `879d1653d1b24b86dc707b52283cd13dbc73f3e8ad56dcfdf1515aee64064444`.
- R54 same-owner projection: `OwnedResidualProjectionR54.lean`, `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`.
- R45 owner incidence: `InternalPermissionIncidenceR45.lean`, `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`.

## Lanes and boundaries

1. Luna/high source author, ≤480 seconds: write only the patch artifact and R117 Rust handoff. Read only the exact baseline blobs above, using read-only exact-path `git show`; never read dirty source files. The patch must be a unified diff against the pinned `candidate_receiver.rs` only. Do not create scratch files, worktrees, caches or generated source. No source-tree application.
2. Registered `lean_prover`, ≤300 seconds: write only `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-proof.md`. Map the R116 selected-endpoint and internal-certificate theorem inputs to exact Rust candidate receipt fields/branches; list producer, owner, occurrence, operation identity and endpoint suppliers plus every remaining source/native premise. Do not add another conditional theorem. No Lean/Lake/checker execution.
3. Fresh independent `compiler_referee`, ≤180 seconds, reviews patch hunks against the pinned baseline and proof/source mapping. Attack different registration/state, same-spelling distinct operation, wrong provider endpoint, missing provenance, observer failure leaking into inference, and collisions between numeric namespaces. No application/build/tests.
4. Primary reconciles and checkpoints ≤240 seconds. Total ≤1,200 seconds; Astra 0; no descendants.

No Rust edits, patch application, compiler/Cargo/build/test, Lean/Lake/checker, installation, cache, worktree, mount or environment experiment. Do not repeat R111/R108 resource feasibility work. R108 records the missing hard aggregate 2-GiB Lean output cap; R111 records the unavailable Rust 6-GiB isolated cap. No environment exploration is authorized. Push the reviewed `.patch` as research only. Rust source integration, execution evidence, source/native correspondence, R114 admission transport, soundness, effect hygiene, principality, termination and production remain OPEN.
