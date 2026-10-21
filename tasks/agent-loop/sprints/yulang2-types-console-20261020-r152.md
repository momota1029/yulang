# Yulang2 Types/Console initializer constructor closure — R152

Status: prospective contract; Luna activates only after exact-hash independent review.
Goal: continue the unchanged user objective of proof-backed Yulang inference/evaluation and broad execution of unchanged Yulang2 Web examples. Types/Console are an increment, not the compatibility ceiling.
Parent behavior: Authoritative `notes/design/2026-10-20-r149-types-console.md`. Simple-sub/evaluator A/B, R70/R71, source/native generality, soundness, principality, production remain OPEN.
Y3 baseline: `b7b320d0516208ab4f6aeac14b795f99c6f92cce`, tree `7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`.
Y2 oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`; sample owner blob `web/playground/src/main.ts` `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`; exact 40-library closure in R149 rev5.
Prior evidence: R150 closeout `0686787f6`; R151 closeout `85586bb73`; R150 corrected note/inbox rev2 hashes `4e24792cf29bcdc9c6ece8089a9fec17544fbbeaee6182277897865fe969452e` / `d821420f59143da1c589665ea983ccf29e4a3ff3b305c29de1c5ec948c04603f`; R151 corrected note/inbox rev2 hashes `4a33c4eea94d05c48ca4b364b3cec875b024349362d69cdcaf90238a3c667873` / `45e2cea95f361e7a15226912d9e5b2234eca3428429cbafa2c3566475c193530`. Both corrections are unreviewed and must be adjudicated before acceptance.

## Outcome

Review the exact R150/R151 correction claims. Then trace the finite, pinned Y2 inference body/expression constructor set below to establish which declaration forms produce each `Evaluation` and `BindingFetch`, how body constraint connection differs from root publication, and which paths publish `ComputedDef`. Apply this to the unchanged Types/Console templates and pinned 40-file library, connecting declaration identity to ordered root composition, successful specialization and runtime consumption. Return a reviewed declaration-qualified census/order, or a precise carrier/constructor obstruction. Unknown census/order/Request reachability must stay UNKNOWN; zero does not follow from missing evidence.

## Exact finite Y2 construction manifest

All paths below are blobs in the immutable Y2 oracle commit. This is a finite source manifest, not a wildcard; tests are excluded and must not be run. Any required owner outside the list requires a sequential Luna pin/lease revision before reading.

| Blob | Path |
|---|---|
| `193864814e61c068663bd53ff2ee2c81a2be12c8` | `crates/infer/src/lowering/body/act.rs` |
| `2c71e2094b6f8e8f0a49bbad683f182b7625784a` | `crates/infer/src/lowering/body/act_copy_census.rs` |
| `4f0c29b6dd64743df1e2c8164c69cac8aed55137` | `crates/infer/src/lowering/body/derive_debug.rs` |
| `4030691560d05b1912b8b0abe0a69fd0127f252f` | `crates/infer/src/lowering/body/derive_eq.rs` |
| `d45f0c10400ea328fc58c84353fc2d53af373fff` | `crates/infer/src/lowering/body/error_decl.rs` |
| `fb747e6db395981f9961f30dbf41e9ec6612347a` | `crates/infer/src/lowering/body/impl_decl.rs` |
| `086d42bc63f1c12414a42898671dda22c8ac1084` | `crates/infer/src/lowering/body/methods.rs` |
| `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99` | `crates/infer/src/lowering/body/mod.rs` |
| `b089ff2e17e87f1eea6e5b97835d372e73722b43` | `crates/infer/src/lowering/body/register.rs` |
| `e2d8dd2b078422ee2a4d518becace64d84609628` | `crates/infer/src/lowering/body/role.rs` |
| `2950c27db8fdf5240b62178649d8963ccef818a7` | `crates/infer/src/lowering/body/signature_helpers.rs` |
| `9a660eb5d487a935bf9b75cb5c81892c8b8e6127` | `crates/infer/src/lowering/body/synthetic_role_impl.rs` |
| `8fe0515fc78e01d400fee555f1ea97c438714658` | `crates/infer/src/lowering/body/type_decl.rs` |
| `a406f4f9b7bc8e7e976014f2b348978e002a1191` | `crates/infer/src/lowering/expr/block_local.rs` |
| `e85beb100231264e210062bd56d8532b09b6200f` | `crates/infer/src/lowering/expr/chain.rs` |
| `bf76fa1a18b18e0ccce4b09c6652f22b31b89b11` | `crates/infer/src/lowering/expr/constraints.rs` |
| `724b103cda8b4e2c457aacf0a674372fb191e3d6` | `crates/infer/src/lowering/expr/lambda.rs` |
| `70ff50c91b0a93a7aee832ed6b494d933973fe1c` | `crates/infer/src/lowering/expr/method_body.rs` |
| `5bbedd550c1edf877f4a7c254548ea02f47bcae8` | `crates/infer/src/lowering/expr/mod.rs` |
| `a2869e541aa22484df07a6f4f53ca4928597260d` | `crates/infer/src/lowering/expr/projection.rs` |
| `8289bfdc6a17b2469ae168ac7939d34813fda474` | `crates/infer/src/lowering/expr/tail.rs` |
| `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be` | `crates/infer/src/typing.rs` |

Classification/publication consumers outside that constructor manifest are pinned separately by reviewed R149: module loading/traversal, compiled root composition/module table, specializer, and runtime engine/lib. Y3 carrier pins are the five owners in R151 rev1 and remain at the same baseline.

## Source/proof lane — 600 seconds

First adjudicate R150/R151 correction artifacts at their exact rev2 hashes, including the distinction between `connect_body` and `publish_runtime_root`, and R150's OpDef-only route. Then trace the full admitted finite owner manifest. Source evidence must distinguish all declaration forms and generated/projected roots, preserve success/error branches, identify who sets suppression state, and connect actual sample declarations to outputs without lexical shortcuts. Do not infer source paths from dirty worktrees. Leased outputs only:

The R151 rev2 correction is not accepted as a whole: explicitly withdraw its residual line 55 claim that the OpDef route “finishes with publication true.” The fifth `finish_binding` argument is `connect_body`; publication is separately gated by `!suppress_runtime_roots && BindingFetch::runs_computation()`. Preserve the other R151 correction only to the extent independently established at its exact source pins. Record this adjudication in the R152 evidence and review it independently.

- `notes/theory/2026-10-20-types-console-initializer-certificate-r152.md`
- `tasks/agent-loop/inbox/20261020-types-console-initializer-certificate-r152.md`

If an exact required source path is outside the manifest, stop at its path/blob dependency and request a sequential revision. Do not convert the stop into evidence that the path is absent.

## Implementation lane — 180 seconds

Read-only Y3 implementation handoff. Re-evaluate the HIR/import/candidate/runtime join only after the source evidence is frozen. Preserve `NO_SAFE_CODE_SLICE` unless the reviewed source result establishes a concrete safe boundary. Exact output only: `tasks/agent-loop/inbox/20261020-r152-implementation-handoff.md`.

## Review and resources

Fresh cap 1200s: preparation/pinning 120, source 600, implementation handoff 180, independent review 180, closeout 120. Charge issued allocations. Astra 0, no carryover. Independent review must separately assess predecessor corrections, complete constructor coverage, distinction of constraint connection/publication, omitted cases, exact sample declaration joins/order, specialization success, and Request reachability. Authors cannot review their work.

No compiler edits, tests, builds, executions, expected-output changes or semantic approval. Stop on a missing pin, incomplete declaration identity, or resource boundary. Only Luna owns current state, exact leases and Git.
