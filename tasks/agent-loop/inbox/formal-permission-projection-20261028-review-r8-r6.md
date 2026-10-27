# Independent review: formal permission projection r8-r6

Disposition: accept the bounded scalar-accounting preservation evidence, conditional on the stated Rust/std assumptions. The inventory of sampled owners is useful partial source evidence. It does not establish the full transitive sampler frame or outer H1. No BLOCKING or major compiler-correctness finding established. Two minor receipt findings follow.

## Independence, authentication and method

Reviewer `/root/formal_permission_projection_r8_r6_review`, fresh non-author, no descendants. ACK start clock 2026-10-27 23:12:38 UTC; deadline 23:14:08 UTC. Effective model/effort and session UUID UNKNOWN. Target independently SHA-256 MATCHED `47fb8176e3f82239d178abcd6263f40fa23f328a5f251af0fcd84bfda6f27322`; amendment05 MATCHED `86066eff5db9b1898c81431ffe0a425cea0d617e5d86f79e9973f1460161c492`; all 30 effective manifest rows MATCHED in separate successful python3 authentication (chunk `0d4d18`, exit 0) before compiler source-body reads. Initial contract/handoff reading preceded this byte check; no compiler source body did. Authentication establishes byte identity, not producer execution history.

Read root/base instructions, design-authority rules, Authoritative top-level inference principles, amendment05, proof skill's conditional/source distinction, and bounded actual source excerpts. Some combined governance output truncated; exhaustive governance inspection is not claimed. Reused the frozen r8-r4 reviewed context frame without re-auditing it. The producer prose supplied claims to test, not independent evidence. No tests, builds, probes, Cargo, Lean, Git, network or descendants. No test verification or cfg(test) correctness claim. Sole write is this review.

## Technical assessment

Cause first: the open obligation is transitive preservation of whole forests and checkpoint association between root selection and final link. Checking selected roots or the prospective inverse alone cannot repair that missing premise. The receipt addresses one actual contributor: accounting writes are separated from forest-inverse writes, and incomplete composition remains OPEN. It introduces no semantic repair or claimed theorem closure.

Actual lib.rs:16614–16667 computes scalar checked totals and writes payload/counter fields and `retained_bound_growths`. Its errors return before later assignments; no forest vector, graph owner, journal Option, intrusion Undo or forests sequence is replaced. lib.rs:16669–16893 changes incoming event/accounting flags and counters, calls the scalar core, and conditionally calls sampling. Unchanged capacity returns the reservation result; changed capacity can return at event-count/preflight/core/sample failure. These prefixes preserve P/J for the scalar core; they need not restore accounting fields. `From<ConstraintError>` at :4175 is enum matching, not a solver callback. This agrees with the Authoritative policy permitting necessary abnormal-path safety without general restoration.

Journal row reservation at lib.rs:9548/:9597 reallocates `value_rows`/`effect_rows`, not the intrusion vectors or `Undo::forests`; row-seen marking and length/flag/level undo append occur only after observation and reservation success. `observe_typed_route_capacity` at :9253 conditionally samples and returns errors without rollback. Concrete production Vec reservation at :88/:135 uses try_reserve and enum conversion. Under the stated nonreentrant allocation assumptions, distinct live vector owners keep the parent allocations and Undo identity unchanged.

Sampling is a genuine session call: :10774 -> :10791 -> :10821 -> :11017, with additional candidate graph/Undo byte summaries in :10930 onward. The inspected ResourceSampleChecked (:330), fixed-capacity helper (:378), scratch (:8144/:8156), journal (:8444/:8459), and term summary (lib.rs:3720; term.rs:867/:872/:1007) use concrete capacities, scalar payload fields, checked arithmetic and a local overflow Cell. `sample_f4_resource_parts` clones counters (:11143), checks completion (:11357), and publishes counters (:11426). These inspected bodies do not mutate P/J. The term snapshot includes an `expect` for structural storage arithmetic: panic exclusion remains material, as explicitly declared by the producer. Nested intrusion/effect/context byte summary completeness remains unproved; the report expressly retains that limitation. Thus “accounting core preserves P/J” is accepted for its scalar subset and conditionally through sampling, never as an unconditional summary of the entire :16669 call.

The merge's prospective forests append precedes journal/copy calls (candidate_intrusion.rs:624 onward); the copied-bound call supplies capture=false (:657). The insertion macro (candidate_extrusion.rs:708 onward) reserves the selected nested lane, accounts, then pushes. Its origin-evidence call precedes that macro (:750). Actual candidate_effect.rs:552 reaches candidate_context_bound on the unscoped branch; scoped BoundTransport selects None. This supports the unscoped wrapper as an outstanding preservation equation. It does not establish that wrapper's full session effects. Sampling already contains an outstanding transitive premise as well, so the wrapper locator must not be interpreted as the sole remaining gap or a proven globally first unsupported callee.

P still quantifies both COMPLETE parent vectors, allocations and row lifetimes; J retains active journal/intrusion Undo association and exact forest-inverse sequence after the prospective append. The bounded scalar analysis preserves these, and consequently cannot invalidate selected root distinctness/in-range status when those premises already hold. It neither proves those entry premises nor same-checkpoint inverse completeness. No reachable falsifier or successful wrong-image export established.

## Findings

### minor — residual locator is stated more precisely than its inspected evidence

Location: source-r8-r6.md:65 and :85. The frozen receipt names `candidate_context_bound_for(...Ordinary)` as a verified deeper delegation/exact residual. Primary relayed the author's post-freeze correction that this deeper delegation was NOT verified. Treating it as an inspected effect owner would falsely strengthen the source inventory and could hide an intervening session effect.

Violated clause: amendment05 requires concrete transitive callees/effect equations; a locator is not an inspected effect summary. Minimum closure: primary attaches this correction to adjudication/shared records while preserving frozen bytes: the supported locator is `candidate_bound_origin_with_evidence -> candidate_context_bound` (candidate_effect.rs:552); the deeper Ordinary delegation is only a candidate locator, and the complete wrapper/callee frame is UNKNOWN. This review accepts only that corrected interpretation. No further source inspection is required to retain OPEN status.

### minor — requested charge omits a recorded source freeze overrun

Location: source-r8-r6.md:73, :85 and :88. The requested 120-second charge is smaller than the receipt's recorded start-to-freeze interval: 23:08:57 to 23:11:39.608688, approximately 162.609 seconds, including 42.609 seconds after the 23:10:57 deadline. Recording only the grant would overstate remaining capacity. Source reads reportedly stopped earlier; that does not erase writing/freezing time.

Violated clause: amendment05 requires stopping/freezing within the cap and recording observed overrun; the resource ledger must preserve actual known expenditure. Minimum closure: primary records at least the observed 162.609-second interval and 42.609-second cap overrun (or a more accurate independently measured longer interval), retaining prior charges and recalculating budget. This is a process/resource finding, not a forest counterexample or retrospective authorization.

## Gate and runtime disposition

H0, COMPLETE H1, H2, B, D, reachable forest/lifetime, r1 Lean, original parent A/B, source/native, full inference/executor and production remain OPEN. Acceptance is bounded conditional source evidence only. No new source packet, owner, theorem authority or production authority follows. Primary owns adjudication and ledger/shared-record updates.

Freeze clock: 2026-10-27T23:14:09.679904+00:00. Observed review interval from ACK clock: 91.68 seconds; initial command launch-to-first-clock overhead UNKNOWN. CPU time and peak RSS UNKNOWN. Charge reserved 90 seconds once without reclaiming unmeasured time. Reviewer STOP on submission; no further work or writes.
