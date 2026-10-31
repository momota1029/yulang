# R7 independent review

Verdict: **close R7 INCOMPLETE**. The revision-2 artifact is a failed construction; neither theorem types nor axiom sets were audited. No proof or production gate closes.

## Authenticated audit result

Attempt 2 used the frozen 13-root checker plan in the isolated Lean 4.35.0 project. The authenticated receipt reports exit 1, 21.72 seconds, maximum RSS 798444 KiB, and zero printed theorem types or axiom audits. Raw stdout/stderr/status/resource hashes match evidence revision 8. The top-level plan, artifact and copied project inventory pin revision 2. The frozen plan's `manifest_successor_transition` mistakenly retains revision 1. The plan was preserved; supplemental provenance receipt `audit-inputs-2-provenance-supplement.json` (SHA `fc7a09913ea40a463d02e6892bac2897f36589c90aaf48b0e0443cf8ad9a9e3a`) records the correction to revision 2. Evidence records both released invocations and attempt 1 as failed. This permits accurate incomplete closeout, but does not retroactively make the plan internally consistent.

## Proof and source findings

The first remaining diagnostic is `FormalPermissionSourceAllocation.lean:249`: rewriting `ao` in a dependent equality leaves `rd` typed as `PortDecoded … ao.state`, so Lean rejects the rewrite motive. Further diagnostics include termination failures at lines 255, 264, 299 and 309, and a kernel application mismatch at line 239. These are failed elaboration/proof obligations, not demonstrated mathematical counterexamples. A separately authorized repair and a complete successful type/axiom audit would be required.

The 91-entry input manifest has the expected R6-to-R7 artifact successor transition; all other pins match. The attempt-2 copied inputs, frozen artifact, handoff, plan and four raw receipts match their hashes. Comparison to the R6 baseline shows theorem statements, quantifiers, hypotheses and relation constructors unchanged. Within the selected source fragment, recursion order, composed variance, tuple guards, and omitted/negative concrete-port selection align with the pinned source. No additional source contradiction was found.

Remaining modeled premises are substantial: `HelperFrames` assumes preservation rather than executing concrete helpers; `FreshStep` requires availability witnesses; the full permission prefix is omitted; and the R5 application assumes a `SourcePair` witness.

## Gates retained OPEN

Conditional transcription type/axiom acceptance; concrete helper frames and Rust execution correspondence; exact-tree `SourcePair`; permission-prefix preservation; native bridge and entry-State observation; original parent; effect hygiene; consumer residual; unequal transport; soundness; principality; termination; production.

Read-only review. No files edited and no Lean, Lake, checker, Cargo or tests run.
