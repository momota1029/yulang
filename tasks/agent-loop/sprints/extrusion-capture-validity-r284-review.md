# R284 independent review — frozen capture-invariant counterexample

Review-only gate after R284 producer STOP. Grant: fresh Sol Lean reviewer up
to 900s plus Luna's already admitted 300s integration allowance. No producer
renewal. Parent/A/B remains 0->0, original R70 stays OPEN, and no Rust/source
correspondence or production authority is granted.

## Frozen target and inputs

Review the exact candidate invariant and its kernel-checked falsifier, not the
whole-language theorem. The explicit technical input manifest is
`tasks/agent-loop/sprints/extrusion-capture-validity-r284-review-inputs.json`,
SHA-256 `8407c07a92ec751aee9214c7b0c6b868eca7e50a0767fa9b451d2c620cd132d4`.
Luna's preflight found all 26 entries MATCH. Paths are complete
repository-relative paths; do not infer or rebase filenames. Candidate module:
`notes/theory/lean/YulangClosure/OriginalExtrusionCaptureValidityR284.lean`,
SHA-256 `6842d0af28691e18ea6c50f250ff08f14205c5cb45ced3d0c58e07178e30f49c`.
Handoff:
`tasks/agent-loop/inbox/extrusion-capture-validity-r284.md`, SHA-256
`8f4d100930853d61b6d7f883f14955b67c3b79ffb170c76e87aec88d5e4b3407`.

## Mandatory authentication and review order

1. Read/hash only this review contract; return actual identity/hash and WAIT.
2. Luna checks the exact identity and digest, then issues separate GO.
3. The first technical operation hashes the manifest and all 26 exact input
   paths, rendering only match/mismatch results. Stop on any missing path or
   true byte mismatch.
4. After the gate, inspect `OriginalExtrusionWork.lean` definitions consumed
   by R284 before opening the R284 module/handoff. Reconstruct `incomingJobs`,
   `copiedRow`, `step`, and the three Result projections; then inspect the
   R284 candidate and R283 `RowsValid` dependency.
5. Run a focused independent kernel check on the frozen R284 module using the
   pinned Lean 4.35.0 project and the transferred, exclusive
   `notes/theory/lean/.lake/build` lease. Audit all 18 declarations, complete
   types and per-declaration `#print axioms`. No broad build or test suite.

## Questions

- Does `CaptureSourceValid` match the raw and canonical Effect references
  actually used by `incomingJobs`, including its all-indices quantifier and
  kind-separated `qe` map?
- Do the implication, R283 `captureGap` exclusion, and computed row-input
  initialization statements follow for their exact quantifiers?
- Does `viewTailGap` satisfy `CaptureComplete` while the actual funded
  `step` queues Effect row 99 with one Effect row, and return `.next`?
- Is `¬ StepPreservesCaptureComplete` an exact application of the printed
  universal theorem, without hidden assumptions?
- Are all helper/frame theorem types and axioms correct, and are the reported
  18 declarations fully covered by the independent checker?
- Which Work, Visit, external, failure, partial-publication and finite-prefix
  cases are open? Identify the first sound repair premise.
- Does any result reach unchanged R70, Rust/source initialization or mutation,
  A/B, Parent or production? It must not do so without the missing bridges.

The decisive result may be that this candidate predicate is false due to an
invalid published view tail. That is not a source-qualified R70 counterexample
or impossibility result for stronger invariants. No source reachability, Rust,
Cargo, tests, probes, external bodies, semantic changes, writes, Git, or
descendants. Reviewer returns STOP receipt to Luna; Luna owns the history
receipt, adjudication and any later sprint decision.
