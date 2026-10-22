# Sprint R327 — Console Add result and Types selected-import failures

Revision 4 supersedes revision 3 only by adding a bounded HIR diagnostic/repair lease for the newly reproduced Types selected-member import failure. Earlier revisions remain unchanged history.

Status: ACTIVE, solo serial lane. Baseline remains pushed commit `483d26976`; current workspace contains uncommitted R327 changes because `.git` is read-only in this execution environment. Parent goal remains all unchanged Yulang2 playground samples through ordinary inference/execution, with implementation and source/native proofs.

## Evidence carried forward

- Exact complete readbacks authenticate Int Add; selected `int.add` source projection removes its Add FieldTail, but the operator result and dependent `say` Display receiver remain unshaped.
- Full playground lib run: 41 passed, 4 Types failures. Three fail on `DeferredSelectionUnavailable`; the exact selected `Display.say` source projection fails during `with_selected_member_operations` with `SourceImportResolutionUnavailable`.
- Pinned `Display.say` source uses `std::io::out::write: a.show + "\n"`. The selected import route needs an exact failure stage before changing recovery behavior.

## Next work

Trace `with_selected_member_operations` stages for the exact say-member source. Identify the specific path, export, or operation route rejected and compare it with the corresponding authenticated identity in the pinned source indexes. Fix only the source-identity mismatch with a focused regression. Re-run the isolated Types import and inference tests, then the full playground library suite. Keep Console result-row lineage as the next solver premise; do not treat the newly surfaced Types failures as closed by Console projection.

Contravariant `[io]` still denotes open `[io,'e]`, so `[state]` is allowed. Do not close or narrow it.

## Leases and gates

- Solo only; no agents or background workers.
- Leases: `tools/inference-playground/src/lib.rs`, `crates/yu-hir/src/module.rs` (bounded selected-member import diagnosis/repair), this contract, the R327 note, and `tasks/agent-loop/current.json`.
- `candidate_scheme.rs` is frozen with no edits. Keep failed or ambiguous import/selection routes fail-closed.
- The 2400-second R327 cap is shared with prior revisions and does not reset. The exact CLI, source/native proof, R149, all-sample completion, theorem closure, independent review, and production remain open.
