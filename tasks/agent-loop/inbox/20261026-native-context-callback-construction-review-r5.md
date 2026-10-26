# Independent review: native Context callback construction r5

Decision: **ACCEPT** for the frozen fresh staged constructor-to-queue projection and its conditional same-history finish/settlement application. No BLOCKING, major or minor semantic finding within that stated scope. Original whole inference/native correspondence gates remain OPEN.

Reviewer: `/root/proof_review_r5`, independent nonauthor/noncoauthor of this component and its dependencies, generic compiler-referee fallback. Prior B acceptance was independent review, not author participation. No descendants. Applied root AGENTS, unchanged proof-closure/source-scope contract, inference design authority/principles, yulang-lean-proofs and compiler-referee policy already read for this review assignment series.

## Frozen inputs and audit evidence

Recomputed the exact assigned hashes; all match:

| Artifact | SHA256 |
| --- | --- |
| `NativeContextCallbackConstruction.lean` | `b90e44fbbf4c268e1b3dc73c32dfb0de542b640207e2feda6c8acf68d89cbb98` |
| Paired note | `49192c7c42f881a141183484d5270ff0dac2cb0a9066f52fd83e691b0180b7aa` |
| Producer handoff | `ad490b71abd13410a65ec4d31c1f9afa0b526964b77b401b7d3d3d38bd4146cb` |
| `NativeContextCompletion.lean` | `5bc4bb4151087462cfbede6f0d6accece70c41ea5061f1ef100ad081e28344b4` |
| `NativeContextReadback.lean` | `321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2` |

The delivered module and inspected dependency cone (`NativeContextCompletion`, `NativeContextReadback`, `NativeContextExpansion`, `NativeDrainOwnership`, `NativeReplayCurrent`, `NativeMergeExpansion`, `NativeReplayCoverage`, `NativeExecutionHistory`, `NativeReplayAcknowledgement`) match the producer isolated-project copies byte for byte.

Inspected all five logs under `/workspace/scratch/c10e953a5453/context-callback-r5/`, including the complete first failure. `check-01.log` exit 1 contains reserved-binder, map/composition-normalization and let-bound split failures plus one unused-simp warning; these are ordinary elaboration repairs, not a hidden semantic refutation. `check-02.log`, `check-03.log`, `check-04.log` and final audit succeed. No timeout/resource failure is reported. The final audit records pinned Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, and Lake 5.0.0-src+eb6cafb, exact module build and `-j1 -M1024` theorem audit.

`audit-plain.log` is 41,712 bytes; SHA256 `0d55f35bd35b4bd25236c62c6a2061f04bc8c65f4ce516de5d5acca7019607f4`, matching the note/handoff. Independently parsed all **21 unique balanced authored-root audit blocks**, complete types and complete transitive axiom results, and reconciled names against every authored theorem in the module. There are 21 PASS records. Exact axiom-set census: 2 propext; 11 propext+Quot.sound; 8 propext+Classical.choice+Quot.sound. No project axiom, sorryAx or checker bypass was found.

The note's “authored-root origin” table is a mapping/census for these 21 names. It is **not** a complete census of all private/generated originating declarations. No complete all-origin count is claimed or certified by this review. That broader integrated audit remains with the primary. The source inspection and full transitive audits substantiate the bounded authored-root proof claim.

No new Lean invocation was warranted: **zero of two allowed risk-driven checks used**. Clean checker evidence was not repeated. No shared or producer cache was touched.

## Mathematical and operational assessment

`leafPairs` is conditioned on the actual leaf constructor; for `.children` it reads the actual operand outcome, rather than trusting the child-key list stored in the leaf. `operand_emission_exact` obtains that operand outcome and exact ordered collect/admit alignment from `applyEffect`. `admissions_exact_keys` then derives every complete child key. Thus the desired body-list equality is not reintroduced as a field or favorable premise.

All four leaves are covered. Local return, bound and conflict emit no plain queue child, while the original body retains its fiber/conflict information. `filter_children_from_apply` justifies the children case through the actual unregistered inline allowance call. `check_filter_exact` selects the actual weight payload/boundary, `decompose_exact` supplies the complete ordered checks and optional continuation, and `body_emissions_exact` proves the whole list equality. Consumed bodies have no continuation; nonconsumed bodies append the actual continuation AFTER all inline checks. Empty lists, duplicate pair/key emissions and registered bound branches do not disappear through set reasoning.

`emissions` uses zip only behind explicit full-length equality in its applications; `enqueueBody` validates that length before selecting a traversal. A short plan list cannot silently truncate the theorem's children. `batch_complete_keys` is instantiated by a DERIVED list equation. Queue front insertion may change queue order relative to issuance order; the theorems track callback/receipt issuance order and then consume the actual later driver run, rather than assuming a front-inserted queue has the same execution order.

`batch_completes_from_guards` derives successful traversal from per-input raw table/source/validity/reservation guards and the actual current working caller. These guards remain true for subsequent local callbacks because map/relation/task fields and caller frames are preserved. The theorem does not assume a child-complete predicate. Per-plan reservation success and chosen already-readable IDs are still operational inputs; it does not prove memory availability or invent an interner allocation result.

`batch_receipt_serials` follows actual `nextWork` increments and computes the consecutive serial range for every successful prefix. Its Nodup consequence therefore distinguishes repeated identical relation/task emissions, including a batch that stops early. This is occurrence allocation, not reuse of an interned relation as a completion certificate.

`fresh_finish_emissions` requires an actual prepare and finishPrefix using the SAME availability/levels/current map, and uses staged_expand to recover actual decompose. The strongest `guarded_finished_children_settled` then derives both earlier seams: the whole-body emitted-list equality and callback batch completion. Actual current/processing/owner fields and the existing same-history finish constructor produce the seal. Each issued occurrence is preserved through the supplied later Run and read back using the existing quiescent theorem; no independent completed-child witness is supplied.

The strongest root still explicitly assumes successful prepare/finish results, publish availability, exact plan length, raw per-plan guards/reservation successes, the live owner fields, a later history FROM the constructed finish state, and final queue/stack emptiness. These are not erased by this review. Its conclusion is conditional readback, not existence of a settling execution or whole solver termination.

## Timing, source correspondence and omitted cases

Inspected actual source owners `candidate_context_admit`, relation inheritance, `candidate_context_transport_task`, `candidate_zero_word_filters`, `candidate_context_execute_relation`, `candidate_enqueue_evidence`, `enqueue_item`, `pair_is_current`, `dispatch_live_item` and staged drain order. Source Context inline effects occur before discharge publication; Dispatch/memo admission follows Context. Registered bounds can perform synchronous origin/replay callbacks. The actual source's already-discharged branch returns without rerunning those checks.

The pure full-body observation and subsequent batch construction do NOT prove that moving every inline callback after owner admission preserves this native chronology. The note explicitly excludes that timing refinement, retains earlier publication/synchronous bound cuts and assigns actual chronological callback extraction as a remaining seam. This limitation is necessary and honestly stated, so it does not invalidate the local projection theorem.

Fresh staged equality at one map is the accepted application boundary. Cached/already-discharged prefixes and transported recipes are not silently treated as fresh prepare results. Their earlier emitted occurrences must be retained and connected through the actual history; rerunning fresh callbacks is not justified by this module. The note/handoff leave these cases OPEN rather than restricting the original supported source language.

Actual selected interner/task IDs, source-to-event extraction, resource and cancellation cuts, table lifetimes, admission Derived integration, synchronous physical bound/Replay callbacks, Replay-bearing enqueues, Value structured ports and full accepted native return remain original obligations. Stage-1 Derived output stays separate and is not falsely asserted present in driver edges. Full source/Call/effect/world meaning, original shared scoped witnesses, principality and inference termination remain OPEN. Neither MERGE-EXPANSION-COVER-1, SourceProblem.NativeCorrespondence nor SourceProblem.InferenceSoundness is closed.

## Writer stop

Receipt frozen; **all writes stopped**. Only this exclusive review receipt was written. No reviewed source/note/handoff, imports, compiler/configuration/shared status, Git index/ref, producer scratch/cache or other repository path was modified. No descendants or background checker exist. Prior A/B/C reviews remain complete and stopped.
