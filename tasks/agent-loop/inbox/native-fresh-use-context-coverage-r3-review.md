# Independent review — NATIVE-FRESH-USE-CONTEXT-COVERAGE/r3

Recorder: Luna, transcribed from the read-only report of `/root/native_fresh_use_context_coverage_review_r3` after its STOP receipt. The reviewer had no write permission; the reviewer's verdict below is preserved without adjudication edits.

## Verdict

**REJECT Rust acceptance; retain Lean only as unchecked partial research. Context coverage remains OPEN.**

1. **BLOCKING — Identity is required as a stored observation, so valid nonempty domains fail.**

   Target: `isolated/native-fresh-use-context-coverage-r3/crates/yu-solver/src/candidate_scheme.rs:642`, `:657`, `:4345`, `:5287`.

   `observed_context_closure` inserts identity `ContextId(0)` into `target_contexts`, while `CircuitEvidence.contexts()` emits only IDs starting at 1 (`candidate_context.rs:1090`). Therefore the subset check fails whenever the mapped DAG reaches identity, including the explicit identity-root case. The synthetic identity fixture manually inserts zero into the observed set and hides this discrepancy.

   Authority: r3 contract **Fixed outcome**, identity coverage; pinned `candidate_context.rs:1090` and `:1188`; Lean projection `NativeFreshUseContextCoverageR3.lean:216` also distinguishes logical identity from stored rows.

   Classification: implementation defect.

   Closure: reconcile logical identity with authentic borrowed readback and demonstrate actual module/local identity and shared-DAG completion routes without fabricated stored identity rows.

2. **major — The empty-domain positive test deterministically contradicts the completion guard.**

   Target: `candidate_scheme.rs:8469` and `:638`.

   `ContextMapCoverageObservation::default()` sets `completed_bound_readback` to false, yet the test asserts that its coverage predicate is true. Static evaluation establishes failure; no test execution was performed.

   Authority: r3 contract **Fixed outcome** and **Required evidence and falsifiers**, items 1–2: empty completed routes must be supported, while pre-bound routes cannot count as completed.

   Classification: implementation/test construction defect, without an approved specification change.

   Closure: distinguish completed empty evidence from unavailable pre-bound evidence in the fixture and exercise both through their actual consumers. Changing the expectation merely to match the current predicate would not establish empty-route coverage.

3. **major — Mutation evidence does not establish the promised source-root and native-map checks.**

   Target: `candidate_scheme.rs:637`, `:8457`; Rust handoff **Frozen implementation**.

   The predicate never reads `source_roots`. Changing that field alone leaves the verdict unchanged; the fixture additionally modifies `source_contexts`, causing its advertised root mutation to fail for another reason. Tests mutate synthetic copied sets rather than a native constructed FreshUse map with unchanged independent source/readback evidence. There is no actual restored/discharged-parent specimen.

   Authority: r3 contract **Required evidence and falsifiers**, item 2, explicitly requires mutations against unchanged construction/readback evidence, including replacement keys, source roots and intervening restoration.

   Classification: incomplete implementation evidence.

   Closure: demonstrate the specified mutations against authentic construction and readback, including independent-root disagreement and actual module/local/restoration cases.

4. **major — Pre-bound suspension has no explicit coverage result.**

   Target: `candidate_scheme.rs:5265` and `:5271`.

   These suspension branches return ordinary `Ok(())`; no coverage API returns `Partial/Unavailable`. A private false completion marker prevents the predicate from accepting a default observation, but does not supply the explicit result promised by the contract and handoff.

   Authority: r3 contract **Fixed outcome**, last sentence of its restoration paragraph, and **Required evidence and falsifiers**, item 2.

   Classification: missing contracted behavior in the research instrument.

   Closure: expose and exercise an explicit unavailable/partial coverage disposition at the suspension cut, without treating routine scheduler progress as completed evidence.

5. **BLOCKING for gate closure — Neither native coverage nor a reachable successful restoration counterexample is delivered.**

   Target: `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR3.lean:163`, `:228`, `:297`; proof handoff **First remaining premise and parent application**.

   `completed_exact_domain` derives domain equality from an explicit abstract transition run; its hypothesis does not simply restate domain equality. However, native execution erasure remains unproved. `attached_target_observed` proves observation of an actually attached child, without connecting every prepared map image to such an attachment or proving weight completeness. The local witness permits a discharge update but provides no reachable restoration trace causing it. The restoration driver at `candidate_extrusion.rs:1008` drives descendants and supplies no inspected noninterference argument. Thus neither broad coverage nor its native refutation follows.

   Authority: r3 contract **Fixed outcome** and **Required evidence and falsifiers**, items 3–5; amendment **Preserved limits**; `Contracts.lean:128`; proof skill **Fix the claim and source correspondence**.

   Classification: unresolved proof/source correspondence obligation, accurately disclosed by the proof producer.

   Closure: establish native trace interpretation plus restoration noninterference or compensating observation coverage, or supply the exact reachable successful native counterexample. Pinned Lean checking and complete theorem axiom audits are additionally required before any checked-proof claim.

No existing expected output, golden, diagnostic or semantic test name was changed in the target diff. No approved semantic change is established. The existing API route remains viable for further investigation; this review does not establish impossibility.

## Authenticated hashes

```text
base contract  d6fc97fde87e8c8a0c0eb0cb8afb140029a0428aedcde6f82b1f162c4bc21725
amendment      dc7389b53d773c4c742af556f4b6d5123821df84bdddb7df97afd7a0ac549fc4
Rust source    9279fcb9bd1580655b7db4541c27338cc3a48ac711f06197cd3ee250b5315923
Rust handoff   23c3b76c95562b838c45f76470483c364cf6e77ba36d8e9de02de1411973ffd5
Lean source    735c0711151c4605d40b338792327f30af80e9740cce346b65517df722543d46
Proof handoff  71d47a6b05871cf4cb676da08eae388b562c33bd7075a97cbf81ad11427625ef
Restoration    80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61
```

Other inspected Rust dependency pins matched. Source was inspected before producer handoffs.

## Reviewer STOP receipt

Reviewer `/root/native_fresh_use_context_coverage_review_r3`; requested Sol/high, observed model/effort UNKNOWN. Review completed within the original 600-second grant; retry message did not renew it. No writes, descendants, Git, Cargo/tests/build, Lean/Lake or checker invocation. No theorem types were kernel printed and no axiom audits were performed. Full FreshUse, returned-root, source/native, parent and production gates remain OPEN; `H_u` remains AUTHORITY_BLOCKED.
