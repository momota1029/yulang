# Sprint NATIVE-FRESH-USE-CONTEXT-COVERAGE/r3 — existing-API Context closure coverage

Status: CANDIDATE until Luna records live admission and exact leases in `tasks/agent-loop/current.json`.
Branch / current primary baseline: `yulang3` / `1d59e3acc`.
Research base: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`, overlaid only with the three pinned candidate owners below. r1/r2 artifacts remain frozen partial evidence and are not copied into this candidate.
Authority: unchanged user goal for Yulang inference/executor soundness and effect hygiene. This sprint is limited to authentic Context closure/map coverage through existing pinned APIs. It grants no production/API change, full FreshUse validator, returned-root theorem, source-semantic change, expected-output edit, H_u authority, or parent closure.

## Fixed outcome

Establish or refute exact Context-map coverage at actual completed FreshUse consumers, using the existing `State.retained_input` / `CircuitEvidence` borrowed readback path and the pinned rename/transport owners. This is a Context observation and coverage gate only. It must not claim payload transformation correctness, full FreshUse validation, Contribution/View identity authentication, root-image correctness, or original source/native soundness.

Derive source relation roots independently from every `graph.bounds` entry carrying a relation. Capture the actual pre-rename `relation_context` roots before constructing the map. Compute the exact rename source domain from the reachable ContextExpr DAG, including identity handling, and establish exact map key coverage. At the completed core return, collect target contexts through both endpoints of every touching FreshUse transport dependency and their child/weight closure. Prove that every expected mapped root and its descendants are observable, and fail closed for any missing source/target/child/weight observation or extra/missing map key.

`retained_input` may overapproximate contexts selected for broader certificate duties. Do not define the expected rename domain as the entire selected context set. Authenticate exact key domains separately from target observation coverage.

Analyze `relation_context` at preparation and later bound admission. Bound restorations can mutate discharge state between those reads. Prove stability or establish sufficient captured-root/coverage evidence under the actual operations; do not assume the needed stability or coverage as a theorem hypothesis. Cover module completion, local completion, shared DAGs, identity, empty/no-relation bounds, discharged parents, intervening restorations, and pre-bound suspension. Pre-bound suspension must return explicit `Partial/Unavailable`; it cannot reuse post-bound evidence.

## r1/r2 adjudication and boundaries

r1 (`tasks/agent-loop/history/native-fresh-use-validation-20261028-r1-outcome.md`) is CLOSED_INCOMPLETE: Rust validator rejected; Lean partial/unchecked. r2 (`tasks/agent-loop/history/native-fresh-use-validation-20261028-r2-outcome.md`) is CLOSED_INCOMPLETE: no validator/theorem delivered. Its independent review found a viable existing-API Context closure route and rejected the producer's blanket `NO_SAFE_CODE_SLICE` claim as unproved. Preserve every r1/r2 artifact and exact hash; neither sprint closes full validator feasibility.

The original `SourceProblem.InferenceSoundness` quantifiers, shared witness, source/native correspondence, effect hygiene, principality and termination remain OPEN. `H_u` remains AUTHORITY_BLOCKED. Only this bounded Context readback/domain coverage claim can be closed here.

## Pinned source inputs

Use exactly the already authenticated r2 pins:

- `crates/yu-solver/src/candidate_scheme.rs`: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`
- `crates/yu-solver/src/candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/candidate_effect.rs`: `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/src/term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- Lean `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- Lean `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- Lean `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` (Lean 4.35.0)
- Lean `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- Lean `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- Lean `README.md`: `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- governed `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- governed `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`

No new source owner or dependency is admitted. Any new dependency returns to Luna for a versioned adjustment. Primary creates a clean isolated r3 workspace from the pinned base and only these three Rust candidate source overlays; all r1/r2 paths stay immutable.

## Exact outputs and leases

- Rust implementation, requested implementer Luna/high: `isolated/native-fresh-use-context-coverage-r3/crates/yu-solver/src/candidate_scheme.rs` only.
- Rust handoff: `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r3-rust.md` only.
- Lean proof, requested lean_prover Sol/high: `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR3.lean` only.
- Lean handoff: `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r3-proof.md` only.
- Fresh reviewer after freeze: `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r3-review.md` only.
- Primary-only Cargo cache: `isolated/native-fresh-use-context-coverage-r3/target`.
- Primary-only Lean scratch/cache: `notes/theory/lean/.task-tmp-native-fresh-use-context-coverage-r3`.
- Luna alone owns current/contract/outcome and Git integration. Children do not dispatch children.

Workers ACK contract hash, role/model/effort, exact write lease, active state and remaining budget before body reads. Runtime metadata not exposed remains UNKNOWN. Fresh reviewer reads source before handoffs and runs no executable checks.

## Required evidence and falsifiers

1. Rust test-only observation records source roots before map construction independently of the candidate map, exact rename-domain keys, and post-bound target constructor/child/weight closure from authentic borrowed readback. Every missing/extra key or unavailable target observation returns explicit failure/partial; no `Ok` path can skip coverage.
2. Mutation falsifiers, against unchanged construction and readback evidence: delete/insert/replace map keys; change source roots; omit target roots, shared children or weights; exercise identity and empty roots; test discharged parents and relation roots after intervening bound restorations. Existing module/local completion routes must use post-bound coverage; pre-bound suspended route returns Partial/Unavailable.
3. Lean proves finite-DAG closure/domain coverage from the pinned rename traversal and transport attachment relation. It proves stability across intervening restoration or narrows the result with an exact counterexample. No theorem assumption may restate the desired coverage. Report complete theorem types and transitive axioms only after the primary's pinned Lean 4.35.0 verification.
4. Fresh independent review accepts frozen exact hashes and verifies the context-root, exact-domain, closure and suspension branches. Primary runs only contract-authorized focused checks after acceptance. The resulting gate, if closed, is `Context observation/map coverage`; full FreshUse validation and root-image/native/source correspondence remain OPEN.
5. A concrete uncovered successful constructor or unstable `relation_context` blocks the broad coverage claim. Stop at the exact first instance and record the finite source trace/counterexample; do not expand to a new owner or production API.

Coverage does not authenticate that a target constructor is the correct transformed payload, nor that a candidate map entry selects the right observable constructor. State these limitations wherever the result is cited.

## Resources and capacity

Fresh envelope 2,600 seconds; no r1/r2 carryover: Rust 500s, proof 1,000s, reviewer 600s, primary verification/integration 300s, contingency 200s (not preauthorized for producers). Two producers, one fresh reviewer, zero Astra. At most two Cargo attempts, aggregate 180s and 2 GiB RSS, one CPU; at most two Lean attempts, aggregate 240s with `-j1 -M1024`; one heavy process at a time. Stop before caps.

Current `UNKNOWN /root/effect_permission_module_environment_source` remains a reserved assignment. Capacity plan is primary + that reservation + two producers + one reviewer + one primary integration reservation = 6. Do not alter any UNKNOWN state or quarantined path. No extra worker slot is admitted.

At sprint end, record complete hashes/outcome and synchronize compact state. Stage no unrelated or quarantined path. Luna is sole integrator and may commit/push only an explicitly reviewed coherent checkpoint after inspecting the full outbound range. The whole user goal remains active beyond this bounded sprint.
