# R38 admission — EFFECT-PERMISSION-RESIDUAL-JOIN/20261031-R38

Contract revision 1: `tasks/agent-loop/sprints/effect-permission-residual-join-20261031-r38.md`  
Contract SHA-256: `6f8420b3c4b3f5ebed311f58bcfbcc1de851d10b7cc47073b8775cd2047fc6e2`  
Inputs: `tasks/agent-loop/sprints/effect-permission-residual-join-20261031-r38-inputs-r1.json`  
Inputs SHA-256: `c2a1093d9b1fccfff74f24281f3236590a43d5ebac425efdb930b853a8e6c3b1`

## Authority and baseline

Luna admits this bounded continuation under the standing user authorization for the unchanged Yulang inference/effects/soundness goal. No new user decision, semantic choice, source domain, production authority, worktree, environment or resource envelope is introduced. Baseline is branch `yulang3`, pushed R37 receipt commit `c6e37750f8b454da95afe0f712710e38b4c94b85`.

R37 is `CLOSED_PASS`; its immutable contract, manifest, admission, source, proof, independent review, stage ledger and outcome hashes were checked against current bytes before its resolved current-state leases are compacted. R37’s technical result and limits remain preserved in its outcome and reviewer handoff. R37 checkpoint `d00417851` and review receipt `c6e37750f` are pushed to `origin/yulang3`.

## Live source seam inspected

The permitted source owners were inspected at their pinned hashes. `FormalPermission` retains parameter index, lambda occurrence, source owner, annotation scope/path, exact row key and concrete source identities; its source comment explicitly says it is not an arrival, provider, contribution or consumer witness. The receiving assembly independently retains the Lambda formal, selected Catch, original provider operation, and source edge whose residual lower/upper endpoints are collected. Its current suppression predicate authenticates provider operation provenance and family at the selected arm, but does not join that result to one retained `FormalPermission` identity. `candidate_call.rs` and `candidate_source.rs` provide the source registration and typed occurrence owners needed to test whether a bounded exact join can be constructed. This is a feasible investigation, not proof that the join exists.

The `candidate_effect.rs` working tree already differs from HEAD by 843 lines before R38 and is a read-only dependency. Its current SHA-256 is pinned in the manifest. It is outside every R38 write lease and must not be changed or staged.

If the exact formal-to-inflow and provider-to-selected-residual identities cannot be authenticated from those permitted owners, Rust must stop before editing and return `NO_SAFE_CODE_SLICE` with the first missing transition. No family-equality fallback or supplied eligibility Boolean is authorized.

## Exact lanes and budgets

- Rust: `crates/yu-solver/src/candidate_receiver.rs` and one handoff only; Luna/high implementer; 1,600 seconds.
- Constructive Lean: `EffectPermissionResidualR38.lean` and one handoff only; Sol/high prover; 1,600 seconds.
- Fresh independent review after freeze: one review handoff only; 1,200 seconds.
- Luna primary, integration, records and Git: 1,600 seconds including 500 seconds closeout; Astra: zero. Total 6,000 seconds; no transfers or renewal.
- Only the exact reads and writes in contract revision 1 are authorized. The existing receiving-runtime quarantine, all other UNKNOWN writers and all quarantined paths remain unchanged.

No builds, Cargo, tests, Lake, formatter, target/cache, copies, scratch, extraction files, worktrees or new environments. Lean verification uses only the pinned read-only stdin method. Rust remains uncompiled.

## Source/review gate

The source lane first establishes all four identities: source formal/annotation action; retained `FormalPermission`; actual provider contribution; selected Catch and residual edge. Any missing link ends source editing with `NO_SAFE_CODE_SLICE`. If authenticated, code must suppress only the joined contribution and forward every unmatched contribution, including same-family/different-boundary and symbolic/unavailable cases. The proof lane independently formalizes guard soundness, empty inflow, preservation of unmatched contributions, and the forwarding/subtraction fold. A fresh reviewer reconstructs the source join and audits all complete theorem types and axioms. No result closes runtime, whole-language, original A/B or production gates.

The live roster was synchronized before admission: `/root` active; `/root/next_action_selector` completed its R38 proposal; all R35–R37 producer/reviewer agents were completed, with R37 reviewer STOPPED. Existing UNKNOWN worker rows and every quarantined path remain preserved. No capacity override or path-lease release was applied for R38.
