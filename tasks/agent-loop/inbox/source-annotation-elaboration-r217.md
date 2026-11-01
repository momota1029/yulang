# R217 source annotation equation — frozen handoff

Sprint ID / contract revision: R217 / 1  
Handoff revision: 2 (sequential correction after primary acknowledgment of R1)  
R1 SHA-256: `be4a32b1699320d1aa6e0491a396425b717d9d914c40262f13166d2c687891d8`  
R1 snapshot: `tasks/agent-loop/history/20261102-source-annotation-elaboration-r217-handoff-r1.md`  
Contract SHA-256: `b3ba54f58a654b22b65467737e25cff37c884cf64ecd798a6754a3d5d694e138`

Assignment: primary source/model author, Luna; session R217. Baseline:
`yulang3` at `ef1873b5e`; original theorem and `supported` domain unchanged.
Outcome class: **candidate / reviewed stopping result**.

## Frozen outputs

- Model: `notes/theory/2026-11-02-source-annotation-elaboration-r217.md`
  SHA-256 `7f70d0cf755c291f6dff8fb0d7cf26fa2e17e0135a65a3f0bbd9e08a91ea6b63`
- Lean: `notes/theory/lean/YulangClosure/SourceAnnotationElaborationR217.lean`
  SHA-256 `e10a84fc095af0cd492f1dd8285eb0136f185b64a29a66deaddc35973c6c08d3`
- Contract: `tasks/agent-loop/sprints/source-annotation-elaboration-r217.md`
  SHA-256 `b3ba54f58a654b22b65467737e25cff37c884cf64ecd798a6754a3d5d694e138`
- Outcome: `tasks/agent-loop/history/20261102-source-annotation-elaboration-r217-outcome.md`

The candidate fixed signature and local value-view equations are described in
the model note and R1 snapshot. They do not instantiate the original Lambda
source rule. The original Lean source stores `Annotation := Nat`, forwards the
ID and selected entry to `sourceFormalRole`, and has no signature table in the
`Source` or interpretation model. The Function row-position mismatch remains:
for `([E] int) -> int`, frozen Oracle puts `Effectful(E, Int)` on `param` and
`None` on `arg_eff`; the current carrier puts the prefix row on the argument
node. Candidate view equations are not Oracle correspondence.

Pinned Lean check passed on the existing project/cache; four theorem axiom
audits contain only `propext` and `Quot.sound`. The fresh independent review
passed only the corrected incomplete candidate. Parent result remains roots
0/4, packages 0/5, parent delta 0, effect-hygiene theorem delta 0.

## Sequential correction and next step

Primary acknowledgment of R1 is recorded in R217 outcome. R1's model hash was
stale (`0462b51e301b0f21d764106f9f1f83a87a8e9f7533be5c14ae1820d813ab395b`);
the corrected model hash above matches the frozen file. No source or Lean
artifact changed, so the mathematical review remains on the same bytes.

The sprint-end selector recommended R218: determine whether the original
annotation meaning can be reconstructed from the actual source inputs, while
keeping `Effectful` value wrappers distinct from `TypeArrow` effect rows and
applying any constructed equation to the unchanged `sourceFormalRole`. Do not
infer impossibility from `Annotation := Nat` alone. Selector recommendation
and completed runtime state are archived in
`tasks/agent-loop/history/20261102-r217-selector-and-resolved-leases.md`.

No Rust implementation slice is authorized until the source/carrier/Oracle
correspondence is resolved. No tests, Rust builds, Cargo, dependency changes,
or new environment were used. User authorized Lean cache creation for this
continuing goal; R217 used the existing cache.
