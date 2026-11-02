# Sprint R247 — successful-history row and term reference closure

Status: ADMITTED under the unchanged goal: Yulang inference soundness and its Rust implementation. Preserve the original parent theorem, all source forms, arbitrary independent satisfying assignment and semantic choices. Parent delta is zero until a justified result is applied at its original edge.

## Fixed outcome

R245 derived and applied the native Parameter term equation and traced current structural return cases conditionally. R246 was reviewed PASS and found no production path where a failed private transaction is followed by another extrusion call in the same session; public readback catches drop that private session. This excludes only failed-route post-rollback reuse. It does not prove the successful-history row/term invariant.

Derive, over successful production histories, the row/term portion of `WCurrent`: every Value/Effect row endpoint used at the two actual ordinary-extrusion calls and every structural child visited by those calls is in its allocated typed region; every term handle is a visible arena member with the claimed tag/sign; any Component association and merged representative are the same valid allocated Value row. Trace initialization, fresh allocation, Parameter/Component translation, structure terms, FreshUse/import, representative merges and bound emission in creation order. Connect the accepted source schedule to work roots and visited children. Apply the derived facts to both actual production calls. A checked constructor's success must not be used to assume unchecked ordinals are valid.

Classify each row/term premise as derived, conditional on a named successful-history invariant, or open at an exact constructor equation. Keep views, members, payloads, evidence, context, R71 raw-slot/fiber coverage and later queue acknowledgement/settlement separate unless a row/term fact directly requires them. Do not turn local source facts into whole-language soundness or production promotion.

Falsifier: an accepted non-test successful prefix constructs an out-of-region/wrong-kind row, invisible/mistagged term, or wrong Component association that reaches a real extrusion root or visited structural child. Hand-built states and test-only routes are not falsifiers.

## Assignment, leases, pins and limits

One registered `prover`, Sol/high, no descendants. Exact write leases:

- `notes/theory/2026-11-02-successful-row-term-closure-r247.md`
- `tasks/agent-loop/inbox/successful-row-term-closure-r247.md`

Maximum 2,400 active seconds. Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined path or Git. If a required owner is outside this manifest, stop source claims and return the exact path/hash need to Luna before citing it.

Baseline HEAD: `da4bcaeeacd369e218e7a9d3b6d85acc6fe72f52`.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/candidate_receiver.rs` | `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade` |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md` | `104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956` |
| `notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md` | `7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e` |
| `tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md` | `647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322` |
| `notes/theory/2026-11-02-production-error-lifetime-r246.md` | `6ec2b144b1976eed7f3fe6e8a2a2ea65f9e23c1836980d288ae695f55a0a408a` |
| `tasks/agent-loop/inbox/production-error-lifetime-r246.md` | `77c8f198805891c9dfd2b8c33f8b03fdda99169aef294138ff6684439734160b` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |

Verify every hash before citing. Record exact output/dependency hashes, successful-prefix cases, actual call applications, residual obligations, resource receipt and STOPPED-writing state. No continuation request or unobserved resource refund is implied.
