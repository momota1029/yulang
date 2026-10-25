# LEAN-CALL-ENTRY-SPINE-20261025/r3 — repair primary composition only

Status: FROZEN ACTIVE CONTRACT. Primary/composer: Luna. Baseline `33cc19a20`, branch `research/simple-sub-intrusion`.

## Fixed goal and boundary

r2 is `FAILED_VERIFICATION / UNACCEPTED`: P Repair and unchanged Q compiled, then Luna's composition failed with unknown branch-local identifiers `consumer'` at four uses. This is an elaboration failure, not a theorem counterexample. Keep the original syntax-only theorem and semantic boundaries exactly unchanged. No P/Q edits, dependency rebuilds, operational rules, Rust/tests/paper changes, source/native claim, Call A/B, inference A/B, effects, or production promotion.

P and Q stay frozen at their r2/r1 source hashes and compiled output receipts. Only the new composition module, new two-invocation JSONL, new query, and reviewer handoff are authorized. All exact new paths must be absent before their first write.

## Exact theorem

In `YulangClosure.TypedCall`, the new `CallEntrySpineComposition.lean` imports only `CallEntryTypingRepair` and `CallPeelingTyping`, and proves the same exact proposition:

```lean
theorem completeCallEntry_typed
    {f : Function} {carrier : Value} {pending : List Adapter}
    {argument result finalResult : Original.Ty}
    (hf : FunctionTyped f argument result)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hpending : AdaptersTyped pending result finalResult) :
    ∃ (mode : Original.Mode) (receipt : ReceiptTemplate)
      (leafArgument bodyResult leafResult : Original.Ty)
      (body : Comp) (consumer : Adapter)
      (leafCarrier : Value) (finalPending : List Adapter),
      PeelFunction f carrier pending
        (.lambda mode receipt leafArgument bodyResult leafResult body consumer)
        leafCarrier finalPending ∧
      CompTyped Original.emptyContext
        (callEntryBody mode leafCarrier body consumer finalPending)
        finalResult
```

The r2 diagnostics are at dependent `cases hleaf` branch references. Repair hypothesis: use the outer existential witness `consumer` in each branch's pending endpoint and P application; retain branch hypotheses `htypedBody`, `hconsumer`, and `hresult`. This is a testable elaboration hypothesis, not evidence of success. Preserve Q's exact lambda witness, result-adapter order and suffix. If Lean rejects the new approach, stop with the exact first output; no automatic repair iteration.

## Frozen inputs and accepted outputs

All hashes must match before composition, verification and review. r2 contract `0f81f286dd3910f48b3f7b49d4f61a6c7a415609a16f0e473fe093bf567c18d4`; r2 outcome `da5f6535b97858bafd02be62ba346b876838d98bf691aa1cd0ee3f1f533cf0bd`; r2 complete verification JSONL `91d4ff52fd157478e4c55d4cb48c61d91e1d9886422853885793a30646dc413b`; P source `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39`; P handoff `cf35a45c656146fd182e5c7b90ea0eb5d69d072696a301a6c4f543de28e856cd`; Q source `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44`; Q handoff `70f2d41c9a785fb5d7d1cee065322c6b68c41bab2ff927f401218c79f20f865b`; r3 accepted dependencies: CoreSyntax `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece`, Contracts `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`, CoreSubstitution `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a`, CoreExecution `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e`, CallContextTyping `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`; toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`, lakefile `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`, umbrella `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f`.

Revalidate P and Q `.olean`/`.ilean` against the successful r2 records before use. If any source or artifact differs, stop; no rebuild is authorized. Require new composition `.olean`/`.ilean` absent before the compile.

## Exact Luna leases and checks

- `notes/theory/lean/YulangClosure/CallEntrySpineComposition.lean`
- `tasks/agent-loop/inbox/20261025-call-entry-spine-r3-verification.jsonl`
- `notes/theory/lean/.lake/call-entry-spine-r3-check.lean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntrySpineComposition.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntrySpineComposition.ilean`
- Fresh reviewer report after verification: `tasks/agent-loop/inbox/20261025-call-entry-spine-r3-review.md`.

Run exactly two Lean invocations, one process at a time: (1) compile the exact composition source; (2) import it and `#check` P, Q existence, delayed argument typing, Q preservation and `completeCallEntry_typed`, then `#print axioms` for each. Each receipt includes full argv/cwd, UTC and monotonic elapsed, timeout/exit, complete stdout/stderr, source hash, exact imported artifact hashes, and output hashes. Append and fsync after each invocation before the next. Stop on any error, timeout, pin mismatch, missing output, signature mismatch, or axiom outside `[propext, Quot.sound]`.

After both pass, freeze all artifacts/receipts and assign one fresh nonauthor `compiler_referee` or `prover` reviewer read-only to audit the exact P/Q/composition statements, mode split, consumer endpoints, nested adapter order, arbitrary pending suffix, output hashes and axioms. Reviewer does no Lean/tests/Git. Luna/composer is ineligible for independent review. No review after failure.

## Resources and parent status

Fresh cap 1,080s, no carryover: composition 240; two Lean invocations and preflight 240; independent review 420; integration 180. Astra zero. One compiler process, one CPU, 1 GiB; each invocation <=120s. No new author assignment. All source/native, execution, effects, Call A/B, inference A/B, and production gates remain OPEN.

Success requires exact theorem, two complete successful receipts, accepted axioms, and CLEAN independent review. Otherwise record `FAILED_VERIFICATION / UNACCEPTED` with the first obstruction. At this material failure/replan boundary the dispatcher was consulted; consult next only on another material failure/change or sprint closure. Luna stages exact paths, inspects the outbound range, then ordinary-pushes coherent commits.
