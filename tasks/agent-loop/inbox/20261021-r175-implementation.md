# R175 implementation handoff — Luna lane result

Contract: `physical-restoration-and-resource-erasure-20261021-r175`, revision 1,
SHA-256 `029356a59ed4c3892548700a4f30610fc1acdf01a160696f27665cec690bcb4e`.

Status: **NO_SAFE_CODE_SLICE; writes STOPPED**. No solver source path changed
in this lane. This is an implementation-owner result, not a proof or review.

## Exact inputs and owner trail

The implementation lane inspected the immutable R175 v6-plus-restoration-owner
snapshot, including `candidate_scheme.rs` (`a08ff106…`), `candidate_context.rs`
(`a08ff106…` is the contract's R174-v6 context pin), `candidate_extrusion.rs`
(`7c9a46d3…`), and `shadow_apply.rs` (`2b0e46f2…`). The baseline/v6 manifests,
theorem and fixture remain as pinned in the contract. No mutable non-owner path
was changed. The worker proof lane is separately reading only those frozen
snapshots.

Relevant constructors in the v6 snapshot:

- `candidate_scheme.rs::begin_candidate_fresh_bound` selects the mapped owner
  and item, constructs a mapped scoped relation and evidence antecedent, then
  calls `candidate_begin_bound_restoration` with `BoundAdmissionCause::FreshUse`.
- `candidate_extrusion.rs::candidate_begin_bound_restoration` calls
  `candidate_insert_bound_with_evidence`, canonicalizes endpoints and retains
  an incremental restoration record. `candidate_step_bound_restoration_child`
  drives each opposite-bound replay and retires the record.
- `candidate_context.rs::fresh_use_fiber_emission` can match the imported
  antecedent, the mapped FreshUse admission, its emitted bound, physical slot
  and constructor-after-append readback. This is a local admission/readback
  join; it does not by itself authenticate the later Apply consumer.
- `shadow_apply.rs` constructs the Apply demand and `invocation_effect` during
  `admit_candidate_fact`. Its query also traverses a Replay recipe and port
  relations, but the R174 review found the attempted path still asks the
  provider's earlier Capture graph to contain the later Apply relation. The
  later constructor does not mutate that immutable graph. Replay ancestry alone
  does not establish both ordered Replay input records and all four consumed
  FunctionPorts for that same provider.

## First unsupported boundary

The missing producer-consumer constructor is the retained bridge from a
particular FreshUse physical emission/readback to the later Apply's ordered
`lower_input` and `upper_input`, followed by authentication of its four
consumed FunctionPort relations. The current retained FreshUse row and physical
emission are not indexed by that later consumer identity. Numeric endpoint
matching or removing the failed Capture-membership predicate would manufacture
the association, so neither is a safe implementation.

Resource erasure remains independently unsupported. R174-v6 clones receipt
identities into frames/undo records and a completion event vector; the vector's
capacity is not in the resource tally, while enclosing struct charges use
`size_of::<...>() - size_of::<Option<SourceDrainReceipt>>()`. That subtraction
does not establish physical layout equivalence. Pinned `module.rs:283–286` shows `HirOccurrenceId` is `{ Arc<HirArtifactToken>,
u32 }` with derived `Clone`; pinned `lib.rs:424–450` shows `CauseId` and
`ConstraintOccurrenceId` recursively clone that Arc-backed identity. These Clone
implementations do not allocate a new identity payload. Ordinary Arc refcount
headroom remains an assumption. Independently, completion-vector reservation,
receipt-bearing frame/origin element layouts, publication, and shared allocator
failure effects still lack source-supported resource equivalence. Editing only
accounting arithmetic would not close that obligation.

## Outcome and next step

No code change is safe before an owner retains the actual provider-to-consumer
association and the evidence resource owner can account for its physical
storage/failure behavior. Keep R174-v6 frozen as **NOT_CLEAN** and
unintegrated. Keep all parent, A/B, source/native and production gates OPEN.
No tests, builds, probes, Yulang/Yulang2/evaluator execution, Git operation,
or unrelated path write occurred. Probe remains `NOT_RUN`.

The proof lane may still establish a useful lemma or the same first missing
constructor from its independent source-level derivation. Luna owns intake,
review and any future exact lease change. This handoff is frozen; writes STOPPED.

## Frozen R175 candidate manifest for proof application

Luna stopped all four solver-code write lanes; these exact candidate bytes match
the R174-v6 snapshot, with no R175 code delta:

```text
24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436  crates/yu-solver/src/lib.rs
a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733  crates/yu-solver/src/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  crates/yu-solver/src/candidate_scheme.rs
2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff  crates/yu-solver/src/shadow_apply.rs
```

Proof application is limited to these candidate bytes and the exact R175
contract. The full parent and production gates remain OPEN.

## Closeout erratum — final review and bookkeeping

Fresh independent review `/root/r175_final_review` returned **NOT_CLEAN** for
integration, theorem promotion and probe authorization. It confirmed the local
physical append/readback lemma and the exact missing supplier and consumer
owners. It found three blocking/major open obligations: authenticate the
admission supplier, connect the same provider through both ordered Replay
inputs and consumed ports including reused/current pairs, and establish
resource/capacity/allocator/unwind erasure. It also identified the synopsis
hash typo above; the explicit four-file manifest and proof note are correct.
The exact review receipt is preserved in Luna's session response and current
state; no code or proof promotion follows.

Erratum: in the first paragraph under “Exact inputs and owner trail”,
`candidate_scheme.rs` is `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25`;
`a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` is
`candidate_context.rs`. No candidate bytes changed.

Current-state lease reason was reconciled from the preparation hash prefix
`54755227` to the frozen handoff hash prefix `adbcda7e`. Resource closeout:
**4,080 seconds charged; 120-second conditional delta reserve expired unused**;
all 4,200 seconds accounted with no carryover. The 240-second closeout grant is
charged in full because trusted elapsed time is unavailable. Probe remains
`NOT_RUN`; all parent/A/B/source-native/production gates remain OPEN. Luna
retains sole Git and integration ownership. This R175 assignment is
**CLOSED_UNFINISHED_RESEARCH**.
