# R285 — derive and prove model storage-reference closure

## Unchanged parent and bounded outcome

The unchanged parent remains R70 ordinary extrusion entry-to-return safety
within the original inference/effects soundness goal. This packet targets the
row-reference safety component only. Preserve original source domain,
quantifiers and semantics. Full R70 W, Rust/source correspondence, Simple-sub
A/B, Parent and production remain OPEN; current parent delta is 0->0.

R283 and R284 independently falsified two predicates that omitted stored
references consumed by the model. R285 must derive reference-safety conditions
from **every stored-field consumer** before attempting a single structural
invariant. Work only in the existing Lean model. No compiler or source-language
claim is granted.

## Required complete inventory

Build a finite, auditable table for every `OriginalExtrusionWork.State` field
and every `Work` constructor. For each stored row reference, record:

- owning field/constructor and exact consumer definition;
- raw row index and any canonical representative read;
- row kind, required bounds conditions and relevant target level;
- whether the reference is consumed now or is latent until allocation,
  queueing, publication, external return or failure handling;
- every model mutation owner that writes, extends, canonicalizes, copies,
  publishes or transfers it.

Include captures and published Effect view tails explicitly, plus all
Value/Effect cell references, queue references, tuple ports, memo keys/images,
parent/child structures, operation roots and stored Work payloads. Cover all
constructors and result paths rather than enumerating only references used by
the two earlier counterexamples. Distinguish raw references from
kind-separated canonical maps.

## Invariant and proof targets

Define a structural `StorageClosed : State → Prop` from the complete inventory.
It must validate every consumed raw reference and its kind-correct canonical
representative. Prove that it implies R284 `CaptureComplete`, excludes both
reviewed `captureGap` and `viewTailGap`, and holds for the existing computed
`rowInput` with no extra caller assumption.

Prove concrete transfer lemmas for the actual allocation, canonical-map
updates, stored-reference publication and queue construction. Then attempt:

```lean
step_preserves_storage :
  ∀ (funds : Funding) (s : State), StorageClosed s →
    StorageClosed (resultState (step funds s))
runPrefix_preserves_storage :
  ∀ (funds : Funding) (fuel : Nat) (s : State), StorageClosed s →
    StorageClosed (resultState (runPrefix funds fuel s))
```

Keep the original universal Funding/state/fuel quantifiers. Cover every Work
branch, `.next`, `.external`, `.failed`, and partial publication before
failure. Apply finite-prefix preservation to the existing computed prefix.
If a theorem fails, freeze the first kernel-checked counterexample or exact
uncovered consumer/mutation owner. No hidden reachability restriction,
circular closure hypothesis, assumed `LocalLaws`, omitted failure case,
stronger unproved predicate premise, or edited model. A coverage table or
stronger predicate alone is not success.

## Frozen dependencies and exact assignment

The explicit 27-input manifest
`tasks/agent-loop/sprints/extrusion-storage-closure-r285-inputs.json`, SHA-256
`931a1fa15351521aeb2f325b0e1822ffe6c8cbd3395b33c0846b8d38281d2ef8`, reuses R284's 26 authenticated inputs and adds the
reviewed R284 receipt. All 27 exact repository-relative paths must match before
proof construction. Keep all earlier Lean modules and R70 parent authority
frozen. Use Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and the existing 11-module import
cone. No dependency/config change.

Producer `/root/sol_r285_storage_closure`, registered `lean_prover`, requested
Sol/high, maximum 2,400s, no descendants. Exact write leases:

- `notes/theory/lean/YulangClosure/OriginalExtrusionStorageClosureR285.lean`
- `tasks/agent-loop/inbox/extrusion-storage-closure-r285.md`
- `notes/theory/lean/.lake/build`, exclusively after stopped-owner
  reconciliation.

Run focused pinned Lake build, direct Lean check and bundled checker for all
new declarations. Report the complete field/consumer/mutation table, exact
theorem types and per-theorem axiom audit, hashes, check commands, omitted
cases and parent application. No broad suite.

## Review and resources

After producer STOP, reserve 900s for a fresh independent Sol Lean reviewer.
Transfer only the cache lease after reconciling stopped ownership. Review the
full inventory against every model consumer, invariants, quantifiers, all
constructor/result/failure cases, computed initialization and theorem/axiom
outputs. Run the focused independent checker on the frozen module. Luna owns
the review receipt and adjudication; reviewer has no artifact write lease.

Luna integration/preparation budget: 300s. Fresh R285 envelope: 3,600s—Sol
2,400s, reviewer 900s, Luna 300s. All prior R282-R284 charges remain consumed.
No refund, renewal or budget reset. Stop at the first genuine counterexample,
uncovered consumer, unavailable checker, scope/dependency expansion or budget
boundary and consult the selector.

No Rust/source/Cargo/tests/probes, external bodies, implementation, semantic
changes, source-domain changes, Git, or production authority. A reviewed
abstract theorem/counterexample is a local model result and does not close R70,
R70 entry premises, source/native correspondence, A/B, Parent or production.
The missing Rust initialization/publication and mutation owners through
`candidate_source` and `candidate_intrusion` stay OPEN.
