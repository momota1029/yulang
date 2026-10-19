# Sprint: braced `if` compatibility proposal — R135 rev5

Status: **FROZEN CORRECTION CANDIDATE; rev4 NOT CLEAN with two MAJOR findings; no compiler implementation authority**  
Branch/baseline: `research/simple-sub-intrusion` / `94bd0aee28508a3316635e6f286a13f153598405`

## Fixed outcome and preserved review evidence

Keep R135's original outcome: prepare a reviewed user-decision proposal for dedicated braced `if` / `elsif` / `else` expression-list bodies, with no implementation or semantic adoption. Existing Y3 syntax remains colon-only. R132 stays `CLOSED_FAILED`; R64/R65, source/native, evaluator and production gates stay OPEN.

Rev4 contract SHA-256: `971fc2692374ef3feadf344a3a4e6fa6d936c9da838879f3f2b78c6e7803143a`. Preserve its two final-review MAJOR findings and frozen artifacts: the predicate's unexpected-child fallback was not stated; and predicate acceptance of multiple spreads was conflated with successful record lowering, which rejects a second spread before lowering it. The rev4 final reviews remain **NOT CLEAN**.

## Required exact correction

Using the unchanged rev4 pins, document the complete `brace_group_is_record_literal` rule: recognized Expr/ExprSpread child-specific checks; Separator permitted; every other child returns false; final result `has_item || !saw_child`. Keep predicate classification separate from parser reachability and subsequent lowering/recovery. Explicitly distinguish genuine empty from separator-only.

Then separate record dispatch from record-lowering success. Multiple valid spread children may satisfy the predicate, but `record_lit.rs` rejects the second spread before lowering its operand. Successful record lowering requires at most one spread as well as successful field/operand processing. Do not claim runtime behavior or infer that the first operand was not lowered.

Preserve the conditional singleton lemma as conditional on actual route and P1–P4. No Y3 empty/record/spread/list meaning, source reachability, runtime output or implementation authority follows.

## Exact lanes and review

- Proof author `/root/r135_braced_if_proof`, sequential handoff revision 2, at most 60 seconds: revise only the existing proof-audit note and exact proof-audit handoff, adding the complete predicate and guarded multi-spread consumer account. Existing followup identity/session remains as observed; do not claim fresh session, UUID or model if unknown. No tests/builds/Git.
- Luna, at most 60 seconds combined: sequentially revise the design and implementation handoff to state these corrections and exact user decision boundary. INDEX is already corrected and remains unchanged. No Y3 decision or implementation.
- The same two independent reviewers from rev4, who are not authors, perform focused delta review of the corrected design/audit/handoffs, 30 seconds each. Do not label rev4 clean retroactively. If either delta is not CLEAN, stop and preserve it.
- Only Luna owns current state and Git. Commit/push may happen only after both deltas are CLEAN and closeout is recorded; otherwise checkpoint the NOT-CLEAN outcome accurately.

## Pins, resources and stop conditions

All authority, baseline, fixture and Y3 pins remain as in rev4. Y2 pins remain: `chain.rs` `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6`; `expr_syntax.rs` `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085`; `record_lit.rs` `88ce8e06f83884fd825402565c52ab1f19e8b9932500036eae495d392a5c990c`; parser group pin and other rev4 pins unchanged.

Rev4 cumulative cap was 1,680 seconds and is fully charged/reserved. Add exactly **120 seconds** for rev5 (60 corrections, 60 paired delta reviews), making cumulative cap 1,800 seconds. Preserve all prior charges and UNKNOWN grants; no refund/reset. Zero Astra. No tests/builds/compiler/CLI/formatter/browser/source edits. Stop if pins change, the deterministic correction reveals another missing owner, budget is exhausted, or any review remains open. User approval and a separate implementation contract are still required before a Y3 syntax or semantic change.
