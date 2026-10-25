# LEAN-CALL-ENTRY-SPINE-20261025/r2 — repair P elaboration, check the unchanged spine

Status: FROZEN ACTIVE CONTRACT. Luna owns authority, composition, verification receipts, review, outcome and Git. Baseline: `3199f25f0` on `research/simple-sub-intrusion`.

## Parent goal and exact boundary

Continue the user's goal to complete Lean proofs of Yulang semantics and inference. r1 ended `FAILED_VERIFICATION / UNACCEPTED`: P's first Lean compile failed after 2.807s; Q, composition, and query were not run. This was an elaboration failure, not a theorem counterexample. Keep the original P proposition, all quantifiers, existing syntax, and all semantic boundaries unchanged. This packet establishes only syntax typing of existing Call entry through finite wraps; it does not establish execution, effects, operational Call A/B, source/native correspondence, inference A/B, or production readiness. Those parent gates remain OPEN.

Accepted dependencies are the r1-frozen source inputs, including checked r3 `CallContextTyping`. Revalidate all pins before launch, composition, checking, and review. Stop on any mismatch. Do not edit the r1 P/Q/composition, existing source modules, Rust, tests, paper, or any unleased path.

## P — exact unchanged proposition in a new module

Author P repair in namespace `YulangClosure.TypedCall` in `CallEntryTypingRepair.lean`, importing only `YulangClosure.CallContextTyping`. Preserve this exact statement:

```lean
theorem callEntryBody_typed
    (mode : Original.Mode)
    {carrier : Value} {body : Comp}
    {argument bodyResult finalResult : Original.Ty}
    (consumer : Adapter) (pending : List Adapter)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hbody :
      CompTyped
        (Original.extend Original.emptyContext
          (match mode with
           | .value => argument
           | .computation => .thunk argument))
        body bodyResult)
    (hconsumer : consumer.input = bodyResult)
    (hpending : AdaptersTyped pending consumer.output finalResult) :
    CompTyped Original.emptyContext
      (callEntryBody mode carrier body consumer pending) finalResult
```

The r1 failure showed dependent `match mode` discriminants accumulating across successive `have` declarations. Repair hypothesis: split on `mode` at the beginning of the entire proof, then construct each branch's entered computation, consumer bind, and pending-adapter derivation within that branch. This is guidance, not permission to alter the proposition. Existing Value entry forces the carrier; Computation entry uses `computationEntryBody_typed`; both preserve the declared consumer and arbitrary pending adapter list. No adapter is evaluated during proof construction.

P author: `/root/call_entry_body_typing`, requested prover Sol/high, exact leases `notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean` and `tasks/agent-loop/inbox/20261025-call-entry-typing-repair-r2.md`; cap 600s. No Lean, tests, Git, descendants, or scratch. STOP after a frozen candidate/handoff or exact obstruction. The author cannot edit the r1 module.

## Q — unchanged r1 candidate, checked in this sprint

Use the frozen r1 Q module `CallPeelingTyping.lean` and its handoff unchanged. Its exact outputs are `PeelFunction`, structural `peelFunction_exists`, `delayArgument_typed`, and `peelFunction_typed` as frozen in r1. This sprint grants no Q source edit or author continuation. First Lean check is pending; Q is not accepted until compiled and independently reviewed.

## Luna composition — exact unchanged parent-facing theorem

Create `CallEntrySpineRepair.lean`, importing `CallEntryTypingRepair` and `CallPeelingTyping`. Preserve exactly:

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

Compose by applying Q existence, then Q preservation, inverting the typed lambda leaf to obtain its mode-specific body derivation and consumer equalities, converting the pending-adapter endpoint using the declared consumer output, and applying repaired P. No extra premise or new operational rule. Luna owns this separate module, the verification JSONL, and `.lake/call-entry-spine-r2-check.lean`; composition cap 240s.

## Frozen inputs

These hashes are inherited from r1 and must all match again before each named phase: `CoreSyntax.lean` `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece`; `Contracts.lean` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; repaired `CoreSubstitution.lean` `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a`; `CoreExecution.lean` `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e`; `CallContextTyping.lean` `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125`; `ControlSyntax.lean` `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0`; r1 contract `77affc0d4d0765c8fffd92fc41653a154ab66bb6598c31c039e4e518d449d4d9`; r1 outcome `11f2478ec74c36fa14c46b66a9027dc9bc8f3fce2e62f6c0356ab8063989c8bb`; Q source `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44`; P handoff `4e39371d8e46f722e025e203247a913a76aac8da4e5bccb7d5ea411bea8a1cd4`; Q handoff `70f2d41c9a785fb5d7d1cee065322c6b68c41bab2ff927f401218c79f20f865b`; `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `lakefile.toml` `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`; umbrella `YulangClosure.lean` `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f`.

r3 binary reuse is allowed only if all five module source hashes and every `.olean`/`.ilean` output hash match the accepted r3 JSONL. Otherwise stop: this r2 packet is capped at nine invocations and does not authorize dependency rebuilds. Before execution, explicitly verify the Q and new-module output paths are absent or match an accepted receipt; never silently trust stale artifacts.

## Verification and review

One Lean process, 1 CPU, 1 GiB, at most 120s per invocation, at most nine invocations. Sequence after source and output pin validation: repaired P; unchanged Q; repaired composition; one signature/axiom query for P, Q existence, delayed argument, Q preservation, and composition. Reuse the accepted r3 dependency outputs only with complete hash receipts. Every invocation record includes full argv, cwd, UTC and monotonic timing, timeout/exit, complete stdout/stderr, source hash, imported output hashes, and produced output hashes. Append and fsync JSONL before the next invocation. Stop on the first failure, timeout, pin mismatch, changed proposition, unexpected axiom, or missing output. Accept only `[propext, Quot.sound]` or a subset.

After successful verification and frozen artifacts/receipts, Luna appoints one fresh nonauthor reviewer (cap 420s) to audit exact P/Q/composition statements, both entry modes, nested distinct-type wraps, adapter order, pending suffix, consumer equalities, receipt preservation, full receipts, and axioms. Author and primary composer are ineligible. No review starts after a failed check.

## Resources, gates, stop and Git

Fresh cap 1,920s, no r1 carryover: P author 600; Luna composition 240; serialized verification 480; fresh review 420; integration 180. Astra zero. Three historical UNKNOWN assignments remain quarantined. No tests or code implementation are authorized.

Success requires exact statements, successful Lean outputs, complete flushed receipts, standard axioms and CLEAN independent review. Otherwise record `FAILED_VERIFICATION / UNACCEPTED` with the exact first obstruction. The r1 bytes stay frozen. Source/native, operational Call A/B, inference A/B, effects, and production remain OPEN in either outcome.

At this sprint-end boundary the dispatcher was consulted. Routine internal steps need no further consultation; consult again on a material counterexample, authority/dependency/lease/resource change, or sprint closure. Luna stages explicit intended files only, inspects the full outbound range, and ordinary-pushes coherent commits. Preserve unrelated untracked Force artifacts.
