# R154 independent receiver review

Verdict: **PASS for the R154 HOLD / NO_PATCH audit disposition; HOLD the complete frozen receiver deletion submission.** No source integration is approved.

Reviewer: /root/r154_review, independent compiler referee. Read-only; no files written. Primary may freeze this exact receipt. Review scope is baseline 41c1582a26a8e80dbaa95171b298fc229a53d4aa and the immutable R154 submission. Source and direct constructor/caller evidence were read before the implementation explanation.

## Authenticated inputs

- Input patch: db49313b2b4dd1e3623f135cc043b4d8be296868c5ec3dbfe90efa6ae5a66438.
- Implementation handoff: 3e43755b3b970c780739727bea80e7d0179a2bd11a02f42cebe3543f262b5d66.
- NO_PATCH marker: 585c06b7c585b42fbf003f0dfbd67df09c6e823b107fe95d6b55b80eebe48af3.
- Proof handoff: 6f8cb681b7e4c19a1d9f4a299f6c50d3aace2e9fa5c7d2ac5f467998366d4279.

All seven committed Rust blob hashes matched the R154 contract. The six patch hunks were reconstructed in memory against the committed receiver, with exact context/deletion checks and no offsets or fuzz. Reconstructed target SHA-256: 3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf, matching the contract. No live dirty receiver/scheme or quarantined runtime bytes were read. Named R117 proof, R118 integration/review and R119 Rust/proof hashes matched the contract; R135 review was read.

## Findings against the frozen deletion submission

**major — unsupported registration/storage coordinate equation.** Location: candidate_receiver.rs baseline 1867–1881, replacement at target 1857 onward; supplier candidate_effect.rs:548–551,1991–2031. The replacement indexes the compact retained-permission inventory with request.registration. Registration addresses all formal registrations; permissions are pushed only for nonempty concrete annotation rows. Consequently registration 7 at packed slot 0 is a valid interface-level counterexample to this equation: the unique registration filter finds the record, while get(7) misses. This violates the distinct-coordinate contract of R117/R119 and R135. It can silently make an evidence reader unavailable. No source-qualified example reaching this private two-definition shape was established; do not report a demonstrated ordinary-inference regression or actual foreign-record acceptance. Minimum closure: preserve the baseline unique registration lookup and carried packed-slot/record association, or independently prove the exact bounded equality invariant at its construction owner before using positional lookup.

**major — matching-operation evidence is removed from the observer.** Location: candidate_receiver.rs baseline 1888–1890 and 5151–5154. Source assembly checks the handled family against the annotation at 3106–3107, whereas provider and selected-arm full operation IDs are separately constructed; source_operation_match at 2937–2951 compares them explicitly. Two operations signal::ping and signal::pong can share a family without being the same operation. Surviving declaration-pointer checks authenticate the provider declaration, not equality to the selected arm. Deleting both full-ID joins therefore leaves the observer unable to supply R116 operationMatch under its previous contract. The residual decision separately checks source_operation_match; this review does not establish erroneous suppression. Minimum closure: retain the full comparison for this evidence interface, or explicitly change and independently justify the observer contract and its consumers.

**major — the R119 ordered same-record member trace disappears.** Location: removed projection/request fields at baseline 234–238,611–615, capture 5156–5191, request transport 4875–4879 and consumer 1883–1897. The submission removes captured position(provider_family), the selected permission pointer/packed slot, and concrete.get(carried_index). A source-derived boolean membership argument can be available for this bounded singleton annotation; it supplies neither the previous ordered-search equation nor unchanged member transport/read. This violates an unchanged claim to R119's selected_retained_member correspondence. Minimum closure: retain the baseline receipt, or deliver a separately reviewed alternative correspondence at the actual constructor and decoder owners. For duplicate vector [4,9,9], first search yields 1; an indexed read of 2 still returns 9, so local equality alone never establishes first-position provenance.

These findings block treating the complete submission as preservation of the existing evidence contract. They are not new theorem counterexamples or proof of a production compiler failure. The baseline already retains the relevant checks; NO_PATCH correctly submits no replacement source.

## Checks with constructor support

The initial owner/batch/live-context pointer block is redundant on the current private path: OwnedResidualProjection::capture binds all three directly from its owner; SourceInternalProjection captures that same owner and verifies same-state inventories. A surviving owner pointer check and physical record joins further constrain mixing. Equal session ordinals alone are insufficient, but no accepted cross-session mix was found through these constructors.

Cached declaration IDs are cloned from the resolved source declarations. Provider occurrence/declaration checks, selected declaration checks and the checked native view/member supplier remain. Catch and owner-call selected-arm ordinals derive from the same schema. These local redundancies do not imply full provider/arm identity.

Permission origin is supplied by unique registration selection, actual FormalEntry action, source Lambda annotation and ordered concrete vector round trips at receiver 4487–4535; incidence-to-retained slice checks remain in SourceInternalProjection near 4600. Equal concrete payload or row numbers cannot substitute for these suppliers. Provider source owner need not equal permission constructor owner; no such equality is recommended for returned/local functions.

## Authority, evidence and limits

Governing authority read: design-authority rule, top-level inference principles, and annotation effect hygiene §§1–1.2. Permission, inflow and residual remain separate; resolved identities matter. Baseline tests for exact signal suppression, same-spelling other-family forwarding, grouped scrutinee and private-envelope ordinary admission were read, not executed. They do not cover all same-family operation or sparse-coordinate cases.

The proof handoff correctly distinguishes interface falsifiers from source-qualified traces and preservation of an observer from actual suppression. Read the implementation handoff's sparse-registration and duplicate-record statements with these same qualifications; current private constructor uniqueness was not refuted.

No builds, tests, Lean/checker execution, source edits, patch application, scratch/cache/environment/worktree creation, Git mutations or descendants occurred. In-memory reconstruction was not filesystem patch application. Compilation, runtime reachability, authentic R39 PRE-state reconstruction, Rust-to-Lean decoding, INITIAL-STATE, CONSUMER, H, original A/B, soundness, principality, termination and production remain OPEN. Review STOPPED; return to the primary for adjudication and exact receipt freezing.
