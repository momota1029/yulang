# Independent review — IDENTITY-ENTRY-ORIGIN-20261027/r1

**Disposition: ACCEPT narrowly as contract outcome 2, with one minor source-locator correction.** No blocking or major finding. Source-to-HIR authenticity and parent application remain **OPEN**.

Reviewer `/root/identity_entry_review` was a fresh non-author reviewer. Review was read-only; no checker/build/test, workspace write, Git operation or descendant was run. The reviewer relied on the author's and primary's Lean receipts and did not claim checker execution.

## Frozen evidence

All five assigned artifact hashes match. All 50 contract pins match. Independently enumerated the complete 29-source Lean project import cone; it exactly matches the handoff inventory and every hash matches. Source inspection found no executable `sorry`, `admit`, project axiom or checker bypass.

Primary independently built the module with pinned Lean 4.35.0. The eleven named theorem audit passed. The full originating audit passed for 39 declarations: only `propext`, `Classical.choice` and `Quot.sound` occur. This is checker evidence under the stated theorem types, not source/native semantic closure.

## Adversarial assessment

1. All eleven new theorem statements derive from `OriginalIdentityRealization.Identity` and existing source constructors. They preserve arbitrary context, occurrence identifiers and whole-expression Apply arguments without freshness assumptions. They introduce no runtime tables, `PairExecution`, receipt admission or annotated callback substitution.

2. The first frontend seam is accurately identified: construct an interpretation from this Identity and enclosing Apply to the matching HIR source root/index, formal ID, Name resolution, source sites/occurrences, labels and lexical/caller environments. Independently supplied `Raw.program` and executable maps do not establish that join.

3. The Callee prefix remains uninstantiated. Its decoded-code, provider lookup, selected Closure, Value role, metadata, old-handle, capacity and dictionary premises stay exposed. Source-only equations establish none of those missing native selection/provenance laws.

4. Source receipt before designated Force, inert Delay/view preparation, native invocation descriptor, post-Force annotated callback receipt, later Name-read receipt and callback-use receipt remain distinct. The unannotated identity has no callback schema; its Observe body records `formal = none`.

5. Original A/B, complete Call, Effect hygiene, shared witness, source receipt admission/readout, complete source/native correspondence, whole-language correctness and production remain **OPEN**. This is not a source counterexample or a general frontend impossibility theorem.

## Minor finding

The frozen implementation trace uses approximate and inaccurate locations at lines 11–12. Correct locations are:

- `program.rs:599–604` for the `label` calculation;
- `program.rs:972–988` for `SourceSite` and `Code` construction;
- `program.rs:721–741` for the Lambda role construction;
- `program.rs:788–804` for Parameter Name resolution/consumption.

This violates the contract's exact owner-location requirement but does not change the verified constructor behavior. The primary records these corrected locators in the integration outcome; frozen producer bytes remain unchanged.

**STOPPED:** review complete; no files or scratch outputs were written by the reviewer.
