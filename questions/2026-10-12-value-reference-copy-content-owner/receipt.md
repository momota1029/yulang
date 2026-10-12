# Receipt — Value-reference incidence on copied rows

Question ID: `2026-10-12-value-reference-copy-content-owner`
Question revision: 2
Approved draft ID/revision: `2026-10-12-value-reference-copy-content-owner-answer`, revision 2
Original worktree/branch: `/home/momota1029/rust/yulang`, `research/simple-sub-intrusion`
Integration commit: `4b4ee56fdb346df48021eb8fbcb20bc172b8463d`
Integrated at: 2026-10-12

## Validation

- The question, current answer draft, and approved answer identify the same
  question and revision 2. The approved answer contains the complete current
  draft verbatim before its approval-provenance section.
- The approval is explicitly recorded as “OK” for draft revision 2, in the
  answering conversation after the full draft was displayed. Its external
  thread locator is unavailable; this receipt does not claim independent
  access to that external conversation.
- The answer names the intended worktree and branch. Its question checkpoint
  `6571cf780c1fbc5e7c3b444995a26e1a9d82cd01` is an ancestor of the integrated
  branch state. The governing parent-copy intrusion design, Source Generalize
  definition, and top-level inference principles have no changes between that
  checkpoint and the integration baseline.
- The directory's unapproved `answer-draft-revision-1.md` was excluded from the
  integration commit.
- SHA-256 at integration:

  ```text
  question.md       20773c40649d2c7bfb7f9f65e450fa2128fec25ffead41b2a58c7be22ec9fda9
  answer-draft.md   2b2d5da4bb207ea6daa1b88ddca965f0df7c3914e4b650f480fea1c74bd26ace
  approved-answer.md b4061f4b9e53ca70f6fe9cfc51b9dfb0ade019b8707a11b8d0024b1b97a19491
  ```

## Outcome and scope

The approved decision is recorded in
[`Value-reference ownership on copied rows`](../../notes/design/2026-10-12-value-reference-copied-row-ownership.md)
and indexed in `notes/design/INDEX.md`. Extrusion and per-use freshening copy
type descriptions and bounds without inheriting Value-reference incidences.
An independent source-owner constructor may assign incidences while preserving
the original resolved-binder targets. Any concrete SCC shortcut requires an
SCC/parent-qualification preservation argument and a computational-cost
justification.

This answer does not approve compiler implementation or F5 cutover. It does
not close source-owner construction on copied rows, actual parent/copy SCC
qualification, equality preservation, soundness, required principality,
complete Call, or effect hygiene. The exact nested `odd`/`even` example has
original cross-level root edges `O → E` and `E → O`; the copied-row rule leaves
that original SCC intact and does not by itself place any extrusion copy in it.
