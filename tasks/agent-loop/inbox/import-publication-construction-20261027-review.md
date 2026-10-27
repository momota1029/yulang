# Import publication construction — independent review

Sprint: `IMPORT-PUBLICATION-CONSTRUCTION-20261027/r1`.
Reviewer: `/root/import_publication_review`, fresh non-author
`compiler_referee`. Review was read-only; shell reads and hashing only.

## Verdict

**ACCEPT both frozen handoffs as a bounded static obstruction report.** No
blocking or major finding. No concrete provider publication, checked theorem,
semantic defect or parent closure was established.

Independent hashes match:

| Artifact | SHA-256 |
| --- | --- |
| Contract | `f8f8e5293bbf79490e2762d53345fc87f148192b89cedc06c6e0930083c30574` |
| Source handoff | `4ea9245a78c01bca1bfe93c5e2dbe420b0c48d2157057387cac4f550cc474204` |
| Proof handoff | `d90465d045fece0d696077b8ea04312086c7c5d0e353ded4e53eb824d86aa08e` |

All 55 rows in the four source/proof pin manifests rehash unchanged, covering
36 unique paths. All four manifest hashes match their receipts.

## Adjudication

`OriginalSourceGeneration.lean:533–545` makes the publication graph fixed
solution data. `publicationCandidate` (`585–605`) reconstructs a record without
reading that graph. `publicationValid` (`607–611`) additionally requires the
exact stored-record equation; `publish` (`613–618`) changes only lexical names,
and `publishGroup` (`777–780`) retains both premises. Replacing only the map
with an everywhere-`none` function preserves candidate reconstruction while
making singleton validity impossible. This is an unchecked definitional
argument, not an executed theorem or source-qualified compiler counterexample.

The provider route matches `bindingsRulesK` (`OriginalSourceGeneration.lean:
377–403`) and the non-Block sequencing rule (`361–373`), but genuine provider
Source/Context/environment correspondence, local admissions and independent
fixed-map realization are still absent. Existing replay construction
(`OriginalEffectHygiene.lean:130–152`) assumes validity. `Prior` formal
admission receives the map independently (`OriginalFormalAdmission.lean:
349–375`).

The Rust path retains provider identity, definition ownership,
dependency-ordered graph storage and FreshUse reconstruction. No correspondence
was shown between its `Graph` (`candidate_scheme.rs:188–215`) and the original
publication record. `CandidateValueObservation` omits invocation/evaluation
effects (`shadow_apply.rs:498–504`). Native Context publication stores a
distinct `PrefixPacket` map (`NativeContextReadback.lean:331–343,471–477`).

Exposure aliasing remains distinct from SRC-J Alias. The resolver fixture
checks common provider identity (`module.rs:4817–4835`); SRC-J Alias copies an
existing Binding and keeps its publication identity
(`OriginalSourceGeneration.lean:430–438`). Complete-publication alias
preservation cannot establish successful installation or exposure
correspondence.

## Minor finding

The source handoff at lines 89–91 cites `candidate_source.rs:2374–2377` for the
comment disabling production certificate creation. The comment is actually at
`crates/yu-solver/src/candidate_source.rs:2381–2383`; the cited lines concern
source-frame setup and resource sampling. This locator drift affects
traceability, not the conclusion. The durable outcome records the corrected
locator.

The relevant resolver and imported-FreshUse tests were inspected, not run.
Lean execution was correctly skipped because the construction gate was unmet;
there are no checked theorem types or axiom audits. All original supported
source, Simple-sub A/B, soundness, Effect hygiene, principality,
termination/progress, complete Call and source/native gates remain OPEN.

The reviewer made no writes and ran no Git, Cargo, Lean/Lake, tests, formatters
or descendants. No processes remain.
