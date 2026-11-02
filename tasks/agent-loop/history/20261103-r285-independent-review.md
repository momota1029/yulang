# R285 independent review — INCOMPLETE at caller-reference boundary

Reviewer `/root/sol_r285_storage_closure_review` (registered `lean_prover`,
Sol/high) STOPPED with no repository writes and no descendants. Charge full
900s; exact CPU/RSS/active time unknown. Disposition is **INCOMPLETE** for the
R285 contract: the delivered local invariant/lemmas were checked, but the
complete-inventory contract boundary and central preservation theorem remain
open.

## Authentication and independent checks

- Review contract SHA-256:
  `1db47594b70f361c8eec8fa30c828171f92893da3a816f2ec620d2069d960c7b`.
- Manifest SHA-256:
  `acce9085a3432ccdcf451cf72a7978fe810991830385bd85cb3a934c4eb6740b`.
- All **32 exact input pins matched**. The first hash attempt used unavailable
  `python`; the `python3` retry succeeded. No technical source was rendered
  before all 32 pins matched.
- Frozen module SHA-256:
  `3000b88435c4cc43a1be5844c1c938470553a30217e351799f50f01bb9f8b9cb`.
  Frozen producer handoff SHA-256:
  `8dc58cf3bd03bc0a1b9b9181690928ad56d6178750b0a06592b1113b908e4afe`.
- On Lean 4.35.0 / commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
  independent focused Lake build, direct Lean check and bundled checker for
  all 19 declarations exited 0. The checker printed all 19 types/axiom blocks
  and returned 19 PASS entries. No `sorry`, `admit`, project axiom or bypass
  appeared in the inspected R283–R285/Work sources. The reviewer had exclusive
  `.lake/build`; the checker removed its temporary audit directory.

Complete axiom lists matched the producer handoff:

| Declaration | Axioms |
|---|---|
| `storage_implies_capture_complete` | `propext` |
| `capture_gap_not_storage` | `propext` |
| `view_tail_gap_not_storage` | `propext` |
| `computed_rowInput_storage` | `propext`, `Quot.sound` |
| `capture_source_transfer_allocate` | `propext`, `Quot.sound` |
| `value_canonical_old_after_allocate` | `propext` |
| `effect_canonical_old_after_allocate` | `propext` |
| `capture_buckets_transfer_allocate` | `propext`, `Quot.sound` |
| `memo_kind_transfer_put` | `propext` |
| `view_tails_transfer_pushed` | `propext`, `Quot.sound` |
| `leaf_refs_transfer_pushed` | `propext`, `Classical.choice`, `Quot.sound` |
| `view_tails_transfer_memo` | none |
| `view_tails_transfer_allocate` | `propext`, `Quot.sound` |
| `queued_view_refs_pushed` | `propext`, `Quot.sound` |
| `bound_perform_retains_state` | `propext` |
| `incoming_perform_retains_state` | `propext` |
| `effect_view_perform_retains_state` | `propext` |
| `computed_rowInput_invalid_caller` | `propext` |
| `no_universal_computed_input_with_caller` | `propext` |

## Boundary finding: caller row references

The producer inventory records `State.operation.caller.lower/upper` and
saved `Parent.operation.caller.lower/upper`, but `StorageClosed` does not
validate them. The model copies these values into a `boundRequest` and stores
them in Parents without dereferencing them as local rows. The R285 contract
requires an inventory of latent/external transfers and every State field, but
its invariant text requires validity of references consumed by the model.

If externally transferred caller endpoints are included in the demanded
stored-row validity predicate, assumption-free initialization for every
`Computed.rowInput caller` is impossible: the frozen checked
`computed_rowInput_invalid_caller` and
`no_universal_computed_input_with_caller` show this for arbitrary
`Request caller`. If those endpoints are opaque until an external consumer,
they can be listed as an explicit external boundary rather than a locally
validated row reference. That leaves a separate source/native obligation;
it does not establish the external request is safe. Luna must adjudicate this
scope reading before accepting the full inventory as contract-complete. No
source reachability or production counterexample follows from the arbitrary
model request.

## Preservation remains open

The exact `select = some (task, popped)` branch remains the unsolved goal
`StorageClosed (resultState (perform funds popped task))` under
`StorageClosed s`. Queue-pop transfer and `perform` closure for all
constructors, funding outcomes and partial publication are unproved. The
reviewer found no kernel-checked falsifier for this branch and does not call
the proof-state goal a counterexample. No `step_preserves_storage`, arbitrary-
fuel `runPrefix_preserves_storage`, or computed-prefix preservation theorem
was delivered.

## Adjudication boundary

This receipt records the review findings, not promotion. The checked local
invariant implies R284 `CaptureComplete`, excludes both reviewed gaps and
holds for arbitrary computed row input. Those declarations and their axiom
reports passed independent kernel validation. Full R285 inventory conformance
and the universal transition proof remain INCOMPLETE pending Luna's boundary
adjudication and the exact open transition premise.

Original R70 production-entry W remains open; so do source/native
correspondence, Simple-sub A/B, Parent and production readiness. Parent/A/B
delta is 0->0; `NO_SAFE_CODE_SLICE` remains. No scope, source, or semantics
change is authorized by this review.
