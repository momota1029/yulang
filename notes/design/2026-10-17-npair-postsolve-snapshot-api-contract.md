# Post-solve candidate snapshot API: unapplied contract

Status: readiness proposal only; not implementation-ready and no code lease.
Sprint `npair-postsolve-snapshot-capability-20261017`, revision 1.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN.

## Decision and exact blocker

The candidate wrapper is consumed-result storage, not a retained session. The
post-solve proof establishes that the original live physical vectors
`InferenceSession.bounds` and `effect_bounds` are read during
`finish_observations` and then omitted from `FrozenInferenceData` and its
construction. `CandidateSolvedResult` therefore cannot presently resolve the
original physical slot described by `PhysicalBoundSlot`. `Graph::bounds` and
that slot descriptor do not replace the source vectors.

The minimum actionable change is to transfer, without cloning, the two physical
vectors into candidate-only retained storage before the consuming session is
dropped. Keep this storage off the ordinary `SolvedModule` result path. A
candidate-only output object could be shaped as:

```text
CandidateSolvedResult {
  data: FrozenInferenceData,
  physical_bounds: CandidatePhysicalBounds {
    values: Vec<VariableBounds>,
    effects: Vec<EffectBounds>,
  },
}
```

`finish_observations` would need a candidate-only return path that transfers
these vectors after their last projection read; `finish_candidate` would attach
them to `CandidateSolvedResult`. This proposal changes ownership and retained
lifetime, not inference meaning. Do not clone either vector. Resource accounting
must charge their retained capacities for as long as the candidate result owns
them, including nested lane allocations; the existing session-freeing
assumption must be revised. This is an unapplied patch direction, not evidence
that moving the vectors is resource-safe under a numeric bound.

## Owner-bound construction and resolution

Only a private method on the returned candidate owner may construct a
borrow-scoped structural view:

```text
CandidateInference::borrow_structural_snapshot(&self)
  -> Result<CandidateStructuralSnapshot<'_>, SnapshotIncomplete>

CandidateStructuralSnapshot<'a> { owner: &'a CandidateSolvedResult }
```

The view accepts no caller-supplied bare `RelationId`, admission ID, emission
ID, graph index or physical slot. Its iterators derive each subrecord from the
same `owner`. Any retained subhandle used in a combining operation must carry
that owner reference and be checked with reference identity (`ptr::eq`) against
the receiver. Same lifetime, equal numeric ID, equal HIR identity or matching
row value does not prove same-owner identity. Private fields and constructors
are required throughout; no lifetime-erased certificate or durable cache.

Construction must return incomplete unless the result is conflict-free and a
reviewed owner-local post-solve quiescence predicate succeeds. Successful
`CandidateInference::solve` alone is insufficient: `Ok` can contain candidate
conflicts, and current `finish_candidate` assertions do not certify that all
processing/replay/restoration work has completed. Define the predicate by
tracing the actual route journal, typed worklist, intrusion pending/dirty state,
context drain/replay continuations and effect processing. Retained historical
records may remain; emptiness of every history vector is not a valid shortcut.
The predicate is not implemented or fully proved by this proposal. Its exact
completion evidence remains a blocker before a code lease.

## Checked live-slot resolver

Resolve the evidence's `PhysicalBoundSlot` against the newly retained original
vectors, never against `Graph::bounds` alone. Check the `RowKey` kind, owning row
ordinal, lane discriminant, slot index, and actual stored operand against the
same-owner admission/emission `BoundKey`, preserving original orientation and
raw row separately from any representative.

| Row kind | Lane | Original vector field |
| --- | --- | --- |
| Value | ValueLowerRow / ValueUpperRow | `VariableBounds.direct_lower_rows` / `direct_upper_rows` |
| Value | ValueLowerAtom / ValueUpperAtom | `VariableBounds.exact_non_variable_lowers` / `exact_non_variable_uppers` |
| Effect | EffectLowerRow / EffectUpperRow | `EffectBounds.direct_lower_rows` / `direct_upper_rows` |
| Effect | EffectLowerAtom / EffectUpperAtom | `EffectBounds.exact_non_variable_lowers` / `exact_non_variable_uppers` |

Out-of-range row/slot, row-kind/lane mismatch, wrong owner row or operand/key
mismatch returns an incomplete result. Never reconstruct a plausible slot from
canonical equality or graph reachability.

## Incomplete evidence and traversal

Use a private result that distinguishes at least conflict, unproved quiescence,
missing retained physical storage, invalid/stale slot, foreign owner,
unsupported provenance, unavailable antecedent and work/storage exhaustion.
Failure returns no partial certificate. `BoundEvidence::admit`'s unavailable
OwnerEmission/ExtrusionLink processing and ordinary-seed antecedents and
FreshUse Replay antecedents remain incomplete. Complete enumeration cannot
synthesize them; require separate reviewed evidence or return incomplete.

The future validator must enumerate every relevant alternative, preserve raw
source occurrences, validate actual FunctionPort endpoints and both ordered
Replay premises, and use a deterministic iterative shared-witness traversal.
Its accounting must include repeated full scans, edge/premise inspection,
branch/fiber-product visits, identity lookups, stack/table/witness capacity,
nested allocations and overlapping growth buffers with checked arithmetic.
No numeric limits or physical allocation theorem are supplied here; those need a
separate reviewed implementation contract.

## Readiness gates and parent application

This design resolves the absent-storage question with one concrete owner-transfer
proposal. It does **not** prove that candidate-only retention is acceptable for
resource policy, establish the post-solve quiescence predicate, prove the
snapshot API can enumerate all relevant evidence, or authenticate unavailable
antecedents. The proof's exact blocker remains OPEN until an owner-authorized
retention decision and fresh code-level contract review. Same-owner construction
is a design requirement, not an existing runtime guard.

No adopted `At(D,w,delta)`, `eta_op`, `realization_op`, source admission,
N-Transport, subtraction, receive consumer, semantic change, production result
or parent closure follows. Preserve the original quantifiers and source domain.
No code, tests, builds, probes, Cargo or source/compiler execution ran.
