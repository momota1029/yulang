# R86 Amendment 02 — one diagnostic-directed proof repair

Sprint: `NATIVE-RECEIPT-JOIN/20261031-R86`.
Base contract SHA-256: `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`.
Prior repair gate: Amendment 01 SHA-256
`7c83569391ab2ec87d81365d87681dcc3366189bb1acc0e3015be52d0521c9b5`.
Slot-1 authorization commit: `c3c34e2a9`; failed result checkpoint:
`f524f2f6c`.

## Diagnostic and exact change scope

Slot 1 used the exact reviewed stdin and exited 1. Independent output review
confirmed seven unsolved-goal errors and `sorryAx` recovery in:

- `readJoin_missing_attachment`
- `readJoin_missing_completion`
- `readJoin_ambiguous_completion`
- `readJoin_bad_guards`
- `readJoin_accepts`
- `readJoinInCuts_ambiguous_completion`
- `readJoinInCuts_accepts`

The residual states retain the dependent `singletonIndex.match_1` / subtype
selection and subsequent monadic match. This amendment reopens exactly two
existing proof-lane outputs for `/root/r86_proof`:

1. `notes/theory/lean/YulangClosure/NativeReceiptJoinR86.lean`
2. `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-proof.md`

Repair those seven proofs by explicitly eliminating singleton-index equations
before unfolding/reducing the reader, or by a minimal helper theorem exposing
the singleton result at its original dependent type. Preserve every existing
definition, theorem name, statement, hypothesis, guard, competitor, cut
predicate, indexed list, and R57/R84 application. No new semantic premise,
Rust edit, source expansion, import edit, or unrelated proof repair is admitted.

## Resource and stop boundary

The original proof grant is 1,400 seconds. The earliest authenticated active
assignment record is commit `41061e95e` at `2026-10-31T13:36:17Z`; at amendment
entry `2026-10-31T13:53:24Z`, at most 1,027 seconds had elapsed and 373 seconds
remained. This amendment grants at most **300 seconds**, and never more than
the actual remainder of the original proof grant. No budget reset, child,
Lean invocation, build, test, cache, target, scratch, worktree, environment,
or Git operation is authorized for the proof worker. Freeze the repaired
candidate and revised handoff with full hashes, the unchanged statement/diff
audit, the exact proposed input recipe/hash, then STOP / WRITES STOPPED.

Luna owns the one remaining Lean invocation (slot 2/2), result capture,
adjudication and Git. A fresh independent reviewer must inspect the exact diff,
all seven repaired declarations, unchanged statements, reconstructed input and
the unchanged conditional scope before a separate exact-input authorization is
committed and pushed. Slot 1 remains charged. Any remaining error, error
recovery, hash drift, semantic change or exhausted resource budget ends R86
without a third call.

This amendment changes only the bounded repair authority and its two output
leases. Source evidence, native extraction limits, selector bridges, original
A/B obligations and production authority remain unchanged and open.
