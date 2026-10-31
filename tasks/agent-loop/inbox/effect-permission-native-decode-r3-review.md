# R3 independent closeout review

Sprint: `EFFECT-PERMISSION-NATIVE-DECODE/20261029-r3`  
Reviewer: `/root/r3_closeout_review` (`compiler_referee`, read-only)  
Assignment: at most 200 seconds; completed within the assignment.  
Primary evidence reviewed: revision 5, SHA-256
`b40c83795726801e1f3fd9fede2b039e7079035563ea91173786c8d437e62af1`.

## Verdict

**ACCEPT the narrow R3 test-only filter repair and authenticated bounded Rust
observation. The decoder-instance outcome remains INCOMPLETE.** No blocking or
major defect was found in the admitted source delta. All original parent,
source/native, effect-hygiene, consumer-residual, unequal-transport, soundness,
principality, termination and production gates remain **OPEN**.

## Findings

- `crates/yu-solver/src/candidate_effect.rs:3468–3482` handles
  `ParameterRow.constructor` separately from the mandatory constructor IDs.
  `Some(id)` must match the same constructor and owner; `None` is excluded.
  Reversing only this change reconstructs the exact frozen R2 source SHA
  `3a8cc6a0d66e08b01ce8d6c8bc770e3c3c9b8ad861779abca09dbf7fb5f4cccc`.
  The block is under the `#[cfg(test)]` module at lines 2573–2574; production
  semantics are unchanged.
- All four R3 raw files match their stored sizes and SHA-256 values. The status
  is 0. The focused invocation passed **1 test, 0 failed, 820 filtered** in
  44.09 seconds; maximum RSS was 1,692,088 KiB, with no timeout, swap or signal.
  Both markers and all 13 required fields occur once. Stderr bytes `[16321,46045)`
  are the exact 29,724-byte extracted observation, matching the stored text and
  SHA-256 `8dc5d61aee002d858cce116fc23cb85afd297395bf181ef35488aea2cb12e556`.
- The test assertions join constructor 1, the exact owner, source origins,
  distinct source paths/effects, allocated rows 22/24, negative nodes 17/14,
  and the exact owner export. This supports bounded identity transport only;
  it does not establish unequal transport or consumer residual behavior.
- The reported `Definition(owner)` scope follows from pinned source:
  `yu-hir/src/module.rs:2553`, `local_source.rs:968–979`,
  `candidate_source.rs:1081–1115,1339`, and `candidate_effect.rs:43–45`.
  Redacted debug strings are not used to infer the join.
- The Lean handoff correctly stops before constructing a decoder instance.
  `FormalPermissionExportWitness.lean:82–167` and
  `FormalPermissionAuthenticatedSiteExport.lean:130` still require the same
  decoded output and the concrete decoder/export equations. Counter 21 has a
  source allocation derivation, but state independence and atomic source-tag
  encoding have no proof or audit. No Lean theorem, artifact or axiom audit
  exists. The stop follows the no-guessing condition.

## Inventory clarification

The prospective R3 Cargo inventory has 318 entries. Its only live-path delta
is the Rust handoff: the prospective revision 1 was 7,236 bytes with SHA-256
`289bac33…6087b1`; the post-run revision 2 is 9,033 bytes with SHA-256
  `30782a4fa34de9f22d8ddf7d7afa9ba2b51322d394713be595a05acf566de2bc`.
This is an expected post-run reporting update. Preserve the prospective
inventory and describe this delta explicitly; do not describe it as a live
zero-delta comparison.

## Review boundary

Assigned source, both handoffs, contract, amendment, input manifest, primary
evidence revision 5, all four raw receipts and the 12 copied Lean inputs were
rechecked. Evidence revision 4 was superseded before review; revision 5 was
explicitly assigned and remained unchanged through the final recheck.

The reviewer used read-only `cat`, `sed`, `rg`, `git diff` and Python byte/hash
inspection. No build, test, compiler, Lean, checker, formatter or write ran.
Actual active CPU time was not measured.
