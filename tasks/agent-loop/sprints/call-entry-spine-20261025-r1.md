# LEAN-CALL-ENTRY-SPINE-20261025/r1 — typed Call entry through wrap spines

Status: FROZEN ACTIVE CONTRACT. Luna revalidated all pins and exact output leases at baseline `e5ea192c0d42bcbc470fee9fb8474d1b8cbee981`; P/Q authors are admitted under disjoint leases.
Branch / baseline: `research/simple-sub-intrusion` / `e5ea192c0`.
Primary: Luna; contract/current/outcome/Git authority stays with Luna.

## Original outcome and exact boundary

Continue the user goal of complete Lean proofs for Yulang semantics and inference. This sprint proves a bounded formal syntax path from an already typed finite `Function` wrap spine to the existing typed `callEntryBody`, using the accepted r3 typed-plugging result. It does not prove Call step simulation, runtime execution, operation/effect preservation, source/native correspondence, inference soundness/completeness, Call A/B, or production readiness. Those parent claims and quantifiers remain unchanged and OPEN.

Accepted source semantics used only to choose the exact existing constructors/equations: `FunctionTyped.wrap`, inert `delayArgument`, pending result adapters prepended inner-to-outer, and the declared lambda consumer. No new semantic constructor or operational rule is introduced.

### P — entry body typing

Author P proves the following exact theorem in `namespace YulangClosure.TypedCall`, importing the checked `CallContextTyping` module. Names are illustrative for binders only; preserve this proposition exactly:

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

Required method: split on mode. Value mode types `valueEntryBody` using force/bind. Computation mode applies the already accepted `computationEntryBody_typed`. Then use the declared consumer and the exact pending-adapter order, via the accepted `adaptersTyped_plugResultAdapters`. Empty and nonempty pending lists are both included. Do not inspect or execute adapter effects during construction.

### Q — finite wrap decomposition and preservation

Author Q owns a disjoint module. Define a purely syntactic inductive relation mirroring the existing `Function` spine and `CallControlStep.peelWrap`; it is not a new transition system:

```lean
inductive PeelFunction :
    Function → Value → List Adapter →
    Function → Value → List Adapter → Prop where
  | lambda
      (mode : Original.Mode) (receipt : ReceiptTemplate)
      (argument bodyResult result : Original.Ty)
      (body : Comp) (consumer : Adapter)
      (carrier : Value) (pending : List Adapter) :
      PeelFunction
        (.lambda mode receipt argument bodyResult result body consumer)
        carrier pending
        (.lambda mode receipt argument bodyResult result body consumer)
        carrier pending
  | wrap
      {inner leaf : Function}
      {argumentAdapter resultAdapter : Adapter}
      {carrier finalCarrier : Value}
      {pending finalPending : List Adapter}
      (rest :
        PeelFunction inner
          (delayArgument carrier argumentAdapter)
          (resultAdapter :: pending)
          leaf finalCarrier finalPending) :
      PeelFunction (.wrap inner argumentAdapter resultAdapter)
        carrier pending leaf finalCarrier finalPending
```

Also prove structural existence for every `f : Function`, `carrier : Value`, and pending adapter list. This distinguishes a constructed decomposition from its typing preservation.

Prove the exact preservation statement:

```lean
theorem peelFunction_typed
    {f leaf : Function} {carrier finalCarrier : Value}
    {pending finalPending : List Adapter}
    {argument result finalResult : Original.Ty}
    (hpeel : PeelFunction f carrier pending leaf finalCarrier finalPending)
    (hf : FunctionTyped f argument result)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hpending : AdaptersTyped pending result finalResult) :
    ∃ leafArgument leafResult,
      FunctionTyped leaf leafArgument leafResult ∧
      ValueTyped Original.emptyContext
        finalCarrier (.thunk leafArgument) ∧
      AdaptersTyped finalPending leafResult finalResult
```

Include and prove the local `delayArgument_typed` lemma required by the wrap case. Match the actual adapter equations: `FunctionTyped.wrap` gives `argumentAdapter.output = inner argument` and `resultAdapter.input = inner result`; each wrap builds a thunk at the inner argument type and changes pending results to `resultAdapter :: pending`. For two wraps, outer result adapters remain before inner adapters in the final execution list (`inner :: outer :: originalPending`). Preserve all receipt syntax untouched. Do not infer decomposition from a typing endpoint alone; use the explicit inductive relation and its existence proof.

### Luna composition — exact parent-facing result

After both authors STOP, Luna composes P and Q in a separate module. Prove:

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

Compose by applying Q, inverting the resulting `FunctionTyped` lambda, extracting its exact mode-specific body derivation and the two consumer endpoint equalities, then applying P. This is a syntax-assembly theorem only; it establishes no `CallControlStep` coverage or execution preservation.

## Frozen dependencies and before/after evidence

All hashes must be rechecked before author launch, composition, verification and review. Stop on any unapproved difference.

| Input | SHA-256 |
|---|---|
| Baseline commit | `e5ea192c0` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| repaired `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| accepted r3 `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `ControlSyntax.lean` (`CallControlStep.peelWrap`) | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| operational type-safety paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| r3 contract | `50314a04521194eb9ec2faef2d122c7afc65f91c58d1cc0936c807d881935d42` |
| r3 accepted outcome | `98b9a65a899264cf739ad0ee42ed104e2c01716f530c9d11b561a9f2a0d1e9d3` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| umbrella `YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |

The exact open source blockers are unchanged: FL12 source applicability/complete Force result frontier, raw/typed Call step correspondence, and original inference A/B. The r3 abstract typing result supplies no premise that closes them. No implementation path is approved; `NO_SAFE_CODE_SLICE` remains in force for dependent runtime changes.

## Two productive proof lanes and integration

- P author: `/root/call_entry_body_typing`, requested prover Sol/high, exact leases `notes/theory/lean/YulangClosure/CallEntryTyping.lean` and `tasks/agent-loop/inbox/20261025-call-entry-typing.md` only; cap 900s.
- Q author: `/root/call_wrap_typing`, requested prover Sol/high, exact leases `notes/theory/lean/YulangClosure/CallPeelingTyping.lean` and `tasks/agent-loop/inbox/20261025-call-peeling-typing.md` only; cap 1,200s.
- Luna composition: `notes/theory/lean/YulangClosure/CallEntrySpine.lean` and `tasks/agent-loop/inbox/20261025-call-entry-spine-verification.jsonl`; primary-owned and may be edited only after both authors STOP. Exact checker source is `notes/theory/lean/.lake/call-entry-spine-r1-check.lean`.
- Each author may prove related private helper lemmas within their exact module. No edits to existing sources, contracts, the r3 candidate, docs, Rust, tests, or other paths. Authors do not run Lean, tests or Git and have no descendants. No mutual import between P and Q.
- Authors run in parallel only after the contract/current state are frozen. Three historical UNKNOWN assignments remain quarantined. With Luna plus two authors, the assignment limit is exactly six including those reservations. Reviewer starts only after both authors STOP and serialized checking is complete.

## Verification, review and resource limits

Fresh aggregate sprint cap **4,080 seconds**, no carryover: P author 900; Q author 1,200; Luna composition 600; Luna serialized verification 480; fresh nonauthor proof review 600; integration 300. Astra zero. One Lean process, one CPU, 1 GiB RAM; each process at most 120 seconds. At most nine invocations. Existing r3 artifacts may be reused only after source and `.olean/.ilean` hashes match their accepted receipts; otherwise compile the exact r3 dependency order within the nine-invocation cap.

Verification order: `CoreSyntax`, `Contracts`, `CoreSubstitution`, `CoreExecution`, `CallContextTyping`, P, Q, composition module, then one query importing the composition and printing the exact signatures plus `#print axioms` for P, Q existence/preservation, `delayArgument_typed`, and `completeCallEntry_typed`. If prior r3 artifact receipts are reused, record and verify their exact hashes as inputs. Capture argv, cwd, monotonic elapsed/UTC, exit/timeout, complete stdout/stderr, source hash and each expected output hash in JSONL, append and fsync before the next Lean process. Stop at the first missing hash, pin change, compile failure, timeout, changed proposition, unexpected axiom or missing output. Accept only standard Lean axioms `[propext, Quot.sound]` or a subset.

Fresh reviewer: read-only, nonauthor, after author STOP and all artifacts/receipts freeze. Audit exact P/Q/composition propositions, wrap equations, empty and nonempty adapter lists, two or more nested wraps with distinct intermediate types, Value and Computation entry, composition application, preserved receipt fields, complete compiler receipts, signatures and axioms. CLEAN requires no accepted blocking or major finding. Reviewer does not run Lean/tests/Git.

Success means P, Q existence and preservation, and the composition theorem all check and receive CLEAN review, with no source/native or production promotion. Falsifiers include reversed nested adapter order, wrong intermediate thunk type, dropped pending suffix, omission of the declared result consumer, value/computation branch confusion, changed receipt, extra premise, custom axiom or incomplete receipt.

## Handoff, stopping and Git

At least two material owners were inspected: `CoreExecution.lean::callEntryBody` and `ControlSyntax.lean::CallControlStep.peelWrap`; these establish the existing construction path but not execution adequacy. While the formal lane runs, source/native work remains independently blocked on FL12-SOURCE-1; no parallel runtime edit is safe. No paper or Rust change is authorized.

A theorem result is applied only to the exact source syntax it names. Original semantics, operation/effect preservation, Call A/B, inference A/B, source/native correspondence and production remain OPEN after this packet unless a separate accepted proof closes them. Luna stages explicit intended paths only, inspects the full outbound range, and uses ordinary non-forced commit/push. Preserve foreign/untracked work. STOP on user request, budget, changed authority/dependency, or need for any new semantic rule. Consult the dispatcher at a material blocker/counterexample, authority/dependency/lease change, integration seam or sprint end—not per lemma.
