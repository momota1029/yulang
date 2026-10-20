# Yulang2 Types/Console ordinary initializer construction — R151

Status: prospective contract; Luna activates only after exact-hash independent review.
Unchanged user goal: implement proof-backed Yulang inference/evaluation and broaden unchanged Yulang2 Web sample execution. R149 Types/Console remain a capability increment, not the compatibility ceiling.
Parent: `notes/design/2026-10-20-r149-types-console.md`; unchanged Types/Console templates, exact outputs and original theorem gates remain in force. Simple-sub/evaluator A/B, R70/R71, source/native generality, soundness, principality and production remain OPEN.
Baseline Y3 commit/tree: `b7b320d0516208ab4f6aeac14b795f99c6f92cce` / `7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`.
Y2 oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`; exact sample blob `web/playground/src/main.ts` `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`; 40-library closure in R149 rev5.
Reviewed runtime dependency: R149 rev2 checkpoint note/inbox `0ce7e3127519e6a17aeb1f2f6d25b24490fbca4ea3644efaf7e1ea8a7b3420c0` / `5d786082cabf7b2ce0f9c463eba13c9b1dc9f0cc1ee8e1f8e9d51a4bb03b2ea4`.
R150 correction dependency: contract rev2 `246edba9d0af7f009e31702ad5ec55db25e491f41bcc20c085e707cb95880657`; correction note/inbox `4e24792cf29bcdc9c6ece8089a9fec17544fbbeaee6182277897865fe969452e` / `d821420f59143da1c589665ea983ccf29e4a3ff3b305c29de1c5ec948c04603f`; R150 closeout `0686787f6` records these as unreviewed.

## Outcome

Independently review the R150 rev2 correction and investigate the actual ordinary Y2 `SyntaxKind::Binding` construction path for the unchanged modules. Connect actual declaration identity and shape to the correct body producer, Evaluation, BindingFetch, publication flag, emitted `ComputedDef`, composed root order, specialization result and runtime consumer. Distinguish ordinary single bindings, header-argument bindings, pattern/destructured bindings, `OpDef`, methods and generated bindings. The R150 OpDef path is not evidence for ordinary/imported initialization.

Return a reviewed declaration-qualified census/order for both exact samples, or a precise obstruction at the first actual ordinary/imported constructor. Do not infer an empty root list, sample failure, or Request reachability from unresolved premises. The R150 corrected result remains unreviewed until this sprint's independent review.

## Source/proof lane — 600 seconds

Read-only immutable-source tracing. Admitted Y2 owners:

- `crates/infer/src/lowering/body/mod.rs`, blob `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`: `lower_block`, `lower_binding`, `lower_single_binding_with_context`, pattern path, `lower_op_def_body`, and binding construction/call sites.
- `crates/infer/src/lowering/expr/mod.rs`, blob `5bbedd550c1edf877f4a7c254548ea02f47bcae8`: `lower_binding_body_expr`, argument-bearing body lowerers, and their expression constructor choices.
- `crates/infer/src/typing.rs`, blob `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be`; `lowering/body/methods.rs`, blob `086d42bc63f1c12414a42898671dda22c8ac1084`; `lowering/expr/tail.rs`, blob `8289bfdc6a17b2469ae168ac7939d34813fda474`.
- R149-pinned module traversal, compiled root composition, specialization and runtime branch owners. The exact 40-library path/blob manifest remains R149 rev5.
- Y3 owners, all pinned at the stated baseline: `crates/yu-hir/src/module.rs` `d8c3e696734463a7bf63d05da00f77f57b9982f4`; playground `lib.rs` `9eeaa94180265970a81f9771a7196e4f0d77008d`, `runtime/program.rs` `fd69daa3d10aeeb4a685766762eef4d80fc0b5de`, `runtime/machine.rs` `4bfd5e244a768ef4cfe61b50fff512d5969b3c88`; `crates/yu-solver/src/candidate_source.rs` `e03d92dcb6016e726fe2748bcfb3f17d52e17cd2`.

Any new owner requires a sequential exact-pin/lease revision by Luna before reading. Do not use the dirty oracle worktree.

Leased source outputs:
- `notes/theory/2026-10-20-types-console-ordinary-initializers-r151.md`
- `tasks/agent-loop/inbox/20261020-types-console-ordinary-initializers-r151.md`

## Implementation lane — 180 seconds

Read-only Y3 implementation-owner handoff. Preserve `NO_SAFE_CODE_SLICE` until both the R150 correction and this source result receive CLEAN independent review. Trace the missing source identity/classification/order carrier from imported declarations through HIR/candidate schedule to RuntimeProgram consumers. Exact output only: `tasks/agent-loop/inbox/20261020-r151-implementation-handoff.md`.

## Resources, review and stop

Fresh cap 1200 seconds: preparation/pinning 120, source lane 600, implementation handoff 180, independent review 180, closeout 120. Charge issued allocations; Astra 0; no carryover from R150. Review must check the R150 rev2 path/specialization corrections, omitted ordinary/pattern/generated routes, exact declaration joins, publication, order, and sample-to-Request premises. Authors cannot review their own contribution.

No code changes, tests, builds, executions, expected-output changes or semantic admission. Stop on missing pinned owners, incomplete sample identity, or resource boundary and report the exact missing constructor. Only Luna grants leases and owns current state/Git.
