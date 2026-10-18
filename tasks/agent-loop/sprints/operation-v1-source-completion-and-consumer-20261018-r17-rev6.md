# r17 revision 6 — corrected resource ledger for r5 source FieldBound

This is a resource-only amendment to r17 revision5; the goal, source, design, owners, exact paths, gates, proof status and semantics do not change. r1–r5 contracts/designs/reviews remain frozen. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0. Baseline last observed `2a3f2a47d5013761f0e0717b0c6073c54c62d36`; local `.git` remains read-only.

Frozen implementation design remains `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r5.md` SHA-256 `d4d7ab94d70522a1860e7764263d69a58855ded856280a6844a788035a314a49`. r5 semantic scope and gates are those in frozen r5 contract `tasks/agent-loop/sprints/operation-v1-source-completion-and-consumer-20261018-r17-rev5.md` SHA-256 `d322f1a33bb5549d3572dd9ac13e6d425070c96a5631364f56c720559fb5d78c`.

## Reconciled budget and exact authority

The previous resource snapshot undercounted reservations by 360 seconds. Reconciled charged work/reservations are: r1 Sol source audit 1200; r1/r2/r3 spec review reservations 360 each =1080; r4 Luna design/API allocation 300; r4 Sol proof/source audit 420; r5 Luna design/API allocation 180. Total **3180 seconds**, no resets and no return of UNKNOWN actual duration.

User has authorized computational/resource adjustments. Add one 360-second continuation: cap **4560 seconds**, charged **3180 seconds**, available **1380 seconds**. Astra 0. Preserve the exact remaining r5 allocation: independent spec review 240s, Luna/high code 600s, independent compiler review 240s, one focused solver run plus integration/state 300s. A failed review gate does not consume code allocation. No automatic renewal.

The unchanged r5 code lease, only after CLEAN independent spec review, covers `crates/yu-solver/src/candidate_source.rs`, `candidate_effect.rs`, optional `shadow_apply.rs` only if required, and additive `crates/yu-solver/tests/candidate_operation_catch.rs`. Other paths remain read-only; expansion requires an exact Luna lease. The unchanged success predicate is a source-generated `FieldBoundV1` whose actual `AnnotationMember <: q-Allowance` edge enters and completes the ordinary typed drain, with receipt only after success. This is static Phase S; runtime Phase R and original theorem closure remain OPEN.

The required review is read-only and should receive this amendment hash plus the unchanged r5 design hash. No additional dispatcher round is needed for the same correction. Only Luna owns current.json and Git. Git writes remain blocked; preserve workspace state and do not claim commit/push.
