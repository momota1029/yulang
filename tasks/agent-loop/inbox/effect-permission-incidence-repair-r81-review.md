# R81 independent proof review

Verdict: **static candidate review PASS; theorem acceptance remains BLOCKING until the authorized exact-input audit succeeds.** No new major or minor correctness finding.

Read-only review. No Lean, Lake, compiler, Cargo, build or test process; no files written by the reviewer, author contact, or descendants.

## Frozen identities authenticated

| Artifact | SHA-256 |
|---|---|
| R81 module | `baba8d0dce9e75dfeb24d5eb6dcf381ec6b103ddaf8aac5b803fcc59142f7c4b` |
| R81 handoff revision 1 | `c18a1ab492d305cd4e7f8b711ffeb97035b7cbaac83ea0371064fc58819f9b84` |
| R81 contract | `33e8f586a6c033af19050d5855c2976058a102c400a4105807097639f199bff4` |
| R81 input manifest | `b70d608d22e0544c9171462bf704a7142f2ee113cecb2c54783b08c1a860ec87` |
| Proposed stdin, 107,431 bytes | `35a379150757ec307d17da62048d64de23ab6e9c014183e1ac5a79bd99daedd6` |

The reviewer independently reconstructed stdin in memory from all 15 slices. Every complete-source hash, slice hash and byte count matches. All twelve pinned source/outcome entries in the R81 input manifest match, including the unchanged R80 module, failed receipts/review, Rust receiver and `lib.rs`. The R81 module and handoff hashes remained unchanged at final review.

## BLOCKING — accepted proof evidence is still absent

Locations: `ConstructedSourceIncidenceR81.lean:95`, `:132`, `:188`, `:316`, `:323`, `:327`, `:342`, `:363`, `:372`, `:383`, `:393`; handoff `:104`.

Static inspection cannot establish that the new local instance limit suffices, the dependent reader normalization elaborates, the concrete output equalities reduce, or the unchanged adversarial `decide` proofs terminate. R81 requires kernel acceptance of the existing R66 constructor, successful finite witness and rejection cases; proof closure forbids treating source inspection as acceptance.

Minimum closure evidence: one separately authorized invocation of the authenticated stdin above, with exit 0, no timeout/errors, all twelve complete theorem types and transitive axiom reports retained, no unexpected implicit premises, and no `sorryAx`, project axiom or native-evaluation assumption. Any changed input requires new authorization and appropriate delta review. This is an evidence gate, not a static source defect.

## Cause and ownership

The diff preserves R80 mathematical statements, primitive checks, inputs and rejection data. Its changes address the earlier failures:

- `PrimitiveRecords` instance at `:85` receives a local synthesis-size limit; its 29 checks are unchanged.
- Role/kind subproofs at `:115` and `:122` expose the finite conversion maps.
- Probe agreement at `:132` normalizes actual reader request/use coordinates before rewriting.
- The successful fixture at `:281–361` supplies explicit data and computed-reader equalities instead of asking `decide` to synthesize equality of the dependent output.

The reviewer independently decoded retained R80 audit-2 stdout and authenticated SHA-256 `58e6d0fcdfa3c8976ef1636dc99cc1d8c72c88152e4b1f21e239ebd8b3dcf08c`. It contains failed `Decidable` synthesis, enum `simp` failures, failed reader rewrite and later finite reduction failures. Six of eight prior theorem reports contain `sorryAx`; none is fresh acceptance evidence for R81.

## Exact construction and invariants

`assemble` at `:188` returns the unchanged `OccurrenceQualifiedConsumerR66.Incidence` directly. All five fields remain: projected probe, actual `sourceProbe` equality, R45 owner reads, R45 identity, and parameter-recipe lookup. No alternate relation replaces the certificate.

`construct` at `:207` takes inventories and coordinates, computes aligned choice and native records, checks `PrimitiveRecords`, then constructs the certificate. It takes no `Incidence`, `Root`, successful `sourceProbe` or global-selection-success input. Lower-level lemmas retain conditional premises; the executable constructor computes them.

The same plan, registration, origin, formal, receipt, permission and parameter recipe remain. Registration ownership precedes Function/entry-image comparison. The registered root comes from the Lambda recipe component through R55 `internalInputs`, not `Formal.nativeRoot`. Annotation and row remain original permission coordinates. R65 readers count all occurrence/slot provenance competitors before resolving fact identity.

The explicit fixture keeps distinct Name/use `100` and Apply/checking `102`, registered Lambda root `300`, formal native root `700`, and duplicate-preserving concrete permission `[7,7,11]`. `finite_constructs_output` establishes the route to `fixtureOutput`, subject to elaboration acceptance.

## Rejections and sibling paths

The candidate preserves the R80 rejection statements for local/global Lambda mismatch, foreign constructor sharing Function and entry image, foreign construction inventory, substituted registration, annotation coordinate, parameter recipe, duplicated slot-0 or slot-2 provenance, parameter-root substitution, and Lambda-recipe root-component substitution. These check modified finite inventories rather than supplied rejection premises.

Existing R77 dependencies still retain duplicate aligned-use/call rejection, foreign owners, wrong use/checking coordinates, invalid Apply fields, and peel cycle/missing-node rejection. No name-spelling or path-specific branch was introduced.

## Source correspondence and boundaries

The reviewer inspected the unchanged Rust owner-selection loop at `candidate_receiver.rs:2499`, selected recipe/parameter/source-Lambda checks, and joined capture at `:4101`. The finite construction matches the ownership and coordinate roles by inspection: complete registration scan, Name/Apply separation, selected recipe and parameter identity, registered Lambda root, positive Function argument-effect and negative entry.

This does not authenticate Rust-to-Lean extraction or compiled Rust behavior. `bridged_target_in_collection` at `:260` still requires R79 `OrderedRoots` and an inhabited `BridgedConstructed`; it does not establish those premises.

## Audit design

The manifest queries exactly all twelve theorem declarations, including four new finite reader/check/output lemmas. The R66 slice contains its complete `Incidence` type and actual `ownerSelection`/`sourceProbe` implementations. The R81 slice contains the whole candidate. No replacement declaration or hidden assumption is inserted by flattening.

Source inspection found no `sorry`, `admit`, project `axiom`, `unsafe`, `implemented_by`, `native_decide` or kernel-check bypass. This does not replace the transitive census. Proposed `#check @…` and `#print axioms …` queries cover the full candidate theorem surface; actual reports must still be inspected.

Remaining open gates: exact-input kernel acceptance, module/import closure, authenticated extraction, R79 `OrderedRoots`, R66 Root and physical/current-slot/admission/relation/ancestry joins, Rust compilation/runtime, original A/B, whole-language soundness/principality/progress/termination, and production promotion.

Reviewer STOPPED / WRITES STOPPED.

## R2 delta review — 2026-10-31

Verdict: **PASS for static review; BLOCKING for theorem acceptance until audit 2 succeeds.** No new major or minor correctness finding. The reviewer remained read-only and ran no Lean, checker, build or test process.

### Authenticated final target

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| R81 r2 module | 27,521 | `3b9e9ac800dccce633c09bf3d7ed0f59f06e910eb42e3a4858e6588f3985bb37` |
| R81 r2 handoff | — | `c90a1931ce3737b98d34cd686ef609d9a112e8d5caf1acaaa7b7c7595ae00e51` |
| Proposed audit-2 stdin | 109,314 | `dba59b391e9a2cfb982bc0e4c97102decdd7ea3ba5414d173f26c2abd47e56e7` |

All 15 complete-source hashes, slice hashes and byte counts match the r2 manifest. All twelve queries remain unchanged. The final module and handoff hashes remained stable at the last check.

### Delta and proof boundary

The module diff against committed r1 `cdc9eb134` contains only:

1. Explicit intermediate normalization in `primitive_records_derive_source_probe`, now lines 171–198.
2. Four fixture proof fields changed from `by decide` to `rfl`: `fixtureChoiceWitness.plans`, `.routes`, `.recipes`, and `fixtureAlignedWitness.uniqueUse`, around lines 314–328.

The reader repair separates the two Option binds. After the computed plan equation, the first `change` reduces the outer bind and projected plan fields, exposing the exact `ownerSelection s target c.plan.targetRootComponent` application. Its agreement equation is then rewritten. The second `change` reduces the resulting bind to the reflexive registration guard. No successful reader result is supplied as an assumption.

The four fixture equalities compare native Plan, Receipt and Recipe lists. Those R55 structures have no `DecidableEq` derivation, so the prior `decide` required unavailable instances. Their literal finite filters and record fields reduce definitionally; `rfl` proves the original equalities without adding instances or changing claims.

All twelve theorem signatures are literally identical between r1 and r2. No definition of `PrimitiveRecords`, `Incidence`, `Constructed`, `construct`, finite inventories, projected records or rejection inputs changed. No assumptions, implicit parameters, typeclass instances, scope restrictions or semantic branches were added. No proof hole or kernel-check bypass appears.

The original r1 handoff is an exact prefix of the final handoff, matching SHA-256 `c18a1ab492d305cd4e7f8b711ffeb97035b7cbaac83ea0371064fc58819f9b84`. The retained audit-1 receipt is authenticated: input 107,431 bytes SHA `35a379150757ec307d17da62048d64de23ab6e9c014183e1ac5a79bd99daedd6`; stdout 31,321 bytes SHA `9e3fe508ef4c09a8194a540de00f3578d715dacffa90ec6f900a4df94bc0ef04`; stderr zero bytes SHA `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; exit 1, no timeout, 10.182 seconds. R1 stdin reconstructed exactly from its retained manifest/source. Its five errors are one failed reader `change` and four failed `Decidable` syntheses. Nine of twelve failed-run theorem reports contain `sorryAx`; the failed run establishes no accepted R81 construction.

The remaining BLOCKING gate is the separately authorized exact audit of the final stdin: exit 0, no timeout/errors, all twelve complete types and transitive axiom lists, no unexpected premises, `sorryAx`, project axiom or native-evaluation assumption. Static review does not substitute for kernel acceptance.

Module/import closure, Rust compilation/runtime, authenticated extraction, R79 `OrderedRoots`, R66 Root and physical/ancestry joins, original A/B, whole-language closure and production remain open.
