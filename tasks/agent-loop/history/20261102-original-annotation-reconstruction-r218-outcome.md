# R218 outcome — original annotation reconstruction

Status: **reviewed conditional source-input audit; original reconstruction and
soundness parent remain open.** No Rust source change or language-semantic
choice.

## Parent result

Original root: `YulangClosure.SourceProblem.InferenceSoundness` in
`Contracts.lean:128–130`, unchanged. The audit found no constructed, authenticated
source law connecting a fixed annotation readout (which a particular `Kernel`
or generic `supported : S → Prop` may capture) to Lambda `sourceFormalRole`
and the declarative source judgment. This is a missing correspondence law in
the inspected original syntax/generation cone. It is not proof that a captured
table cannot exist, not an actual Yulang collision, and not semantic
under-specification.

Parent delta: **0**. Soundness/principality/termination roots remain open;
root count 0/4, package count 0/5, effect-hygiene theorem delta 0. The conditional
Lean construction shows that two distinct external readouts for the same
annotation ID cannot both be selected by one resolver over syntax alone; neither
readout is established as the actual Yulang meaning.

## Lean evidence

Module: `YulangClosure.OriginalAnnotationReconstructionR218`, SHA-256
`757e1aba95e32761360676facdab27ca11b34b4e1b986c8b0f1479ee33a604e6`. Pinned
Lean 4.35.0 / Lake 5.0.0. Primary checker built the module successfully with
the existing project cache, printed all six theorem types, and audited each
with `#print axioms`; all six have an empty axiom dependency list. The
registered leaf first failed before build while Lake attempted thread creation
under inherited `RLIMIT_AS=1 GiB` (exit -6, maximum RSS 24,256 KiB); the leaf
stopped and the primary used the existing cache. No package/environment update,
Rust build or test. Detailed command and receipts are in the model note.

Checked declarations:

- `original_lambda_formal_unchanged`
- `external_readouts_preserve_row_ownership`
- `annotation_trees_distinct`
- `same_annotation_id_distinct_external_readouts`
- `conditional_no_common_source_resolver`
- `no_source_resolver_agrees_with_both_external_readouts`

## Review and evidence boundary

Fresh compiler-referee review R1: no blocking or major findings; three minor
source-accuracy findings. R2 corrected all three and passed exact-delta review.
The final model, contract, and handoff hashes are recorded in `current.json`
and the handoff.

The frozen Oracle checkout is absent. The four-port arrow-row comparison is
inherited from the pinned R217 report and was not independently inspected in
R218; R218 makes no fresh Oracle correspondence claim.

## Artifacts

Frozen SHA-256 values:

- Contract: `edc324dd8f0e5eaf4e0f5da8b6c6310e942215a58d936a48a3dfc0ff8ed882e0`
- Model note: `4d9a622d9ea6beee423b4238d274c5bcf4f0d338d84cb4f111ac709ec823beb8`
- Lean module: `757e1aba95e32761360676facdab27ca11b34b4e1b986c8b0f1479ee33a604e6`
- Handoff revision 2: `580543e103b94a16e5dacd136d3636ac7cfb7b3947f77776489a75f762b7dfb2`
- Contract: `tasks/agent-loop/sprints/original-annotation-reconstruction-r218.md`
- Model note: `notes/theory/2026-11-02-original-annotation-reconstruction-r218.md`
- Lean module: `notes/theory/lean/YulangClosure/OriginalAnnotationReconstructionR218.lean`
- Handoff: `tasks/agent-loop/inbox/original-annotation-reconstruction-r218.md`
- Review evidence: R1/R2 scoped findings from `/root/r218_candidate_review`
