# Directed Stack Weight Implementation Plan

Source: `research/effect-mini-language/directed_stack_weight_principal_letrec_colored_soundness_ja.tex`.

This note records the implementation consequences of the colored soundness draft.
It supersedes older "protect/floor" readings of effect subtraction when they conflict with the draft.

## Core Invariants

- The subtype judgment carries a pair of directed weights:
  - left weight `L: Id -> (leading_pops, family, active_pushes)`
  - right weight `R: Id -> leading_pops`
- Left and right weights are not the same structure.
  Right weights never carry push/family information.
- For one id, the normal form is `pop^m take(H)^n`.
  `take(H); pop` cancels, but `pop; take(H)` does not.
- Different ids commute only at the count-abstraction level.
  Same-id order is observable through the directed normal form.
- Mixed normalization only applies when both sides are present.
  Normalize `L` followed by `R`, then project the result:
  active push remains on the left, pure pop remains on the right.
- Bound entries may store `(type, L, R)` for delayed propagation, but compact display projects:
  positive occurrences to `PWeight(L, T)`, negative occurrences to `NWeight(R, T)`.
- `protect` is not a separate constructor.
  A protected effect variable is `PWeight(take(Empty, u), rho)`.
- Concrete covariant effect annotation is a `Filter(B, T)` check.
  It has no runtime marker after solving.
- Runtime soundness is for normalized, well-bracketed colored marker elaboration, not for arbitrary raw marker sequences.

## Row Split Contract

For a weighted row upper bound:

```text
alpha @ L <: [K; beta]
```

the only head that may be consumed is:

```text
J = K ∩ Common(L)
```

where `Common(L)` is the intersection of all active left-push families.

The split is:

```text
alpha <: [J; gamma]
gamma @ (L minus J) <: beta
```

if `J` is non-empty. If `J` is empty, no residual is created and the comparison continues to the tail.

The residual key is `(source, J, L minus J)`.
The target tail is not part of the key.

Right pop does not affect the row head. It is distributed to the target tail before row split.

Self-tail splits of the shape `beta @ L <: [K; beta]` are no-ops for finite colored observations.
This is the preferred way to stop self-fueling row cycles, together with residual hash-consing.

## Current Implementation State

- `crates/infer/src/constraints/row_effect.rs` no longer combines both sides with:

  ```rust
  weights.left.compose(&weights.right)
  ```

  before row-head subtraction. Row split now computes `Common(L)` from left active stack entries only,
  and carries right-side pop to the residual tail.

- `row_effect.rs` now receives the solver's directed left weight.
  Legacy `poly::types::StackWeight` is only used for surface wrappers and compact materialization.

- `ConstraintWeights::compose_for_replay()` and var-var replay now normalize by W-Mix before applying the
  implementation-side pop-growth caps. This keeps the semantic directed projection before the termination guard.
  The replay normalizer uses the directed `LeftStackWeight`/`RightStackWeight` mix implementation and then
  keeps the solver state in directed left/right storage.

- `ConstraintWeights.right` now uses a dedicated `RightStackWeight`.
  It can represent only pure right pops. Push/floor/filter cannot be stored on the right side structurally.

- `ConstraintWeights.left` uses `LeftConstraintWeight`, a directed left normal form plus a temporary filter carrier.
  It cannot store legacy floor. Surface `StackWeight` wrappers are converted at absorption time, and compact/finalize
  boundaries materialize directed left weights back to `StackWeight`.

- Left-side filters are checked at bound insertion and erased before bounds are stored or replayed.
  Lower bounds check the incoming lower type immediately. Upper and var-var bounds register the filter on the
  source/lower variable so later lower bounds are checked through the existing `lower_filters` path.

- `floor` is not part of the new formal core. The row split path no longer creates new floor residuals,
  and active-family readers now use `StackWeight::active_stack_items()`, which ignores legacy floor entries.
  Replay W-Mix also ignores floor for cancellation/projection because bound left weights no longer contain floor.
  Cleanup liveness also treats only active pushes as live stack ids. Remaining floor code is limited to legacy surface
  wrappers and compact/finalize paths.

- `filter` is currently embedded in `StackWeight`.
  Row split, `Neg::Stack` absorption, and bound insertion treat filter as a separate wrapper/check and erase it before
  residual propagation or replay. Raw wrapper translation still uses `StackWeight::filter` as the temporary carrier.

- Family type arguments are constrained when effect family paths meet in machine-owned set operations.
  Row split, residual subtraction, duplicate row head collection, filter checks, and `Neg::Stack` common-stack checks all
  enqueue invariant argument constraints instead of comparing only the family path.

- Bounds replay and alias replay pop caps are implementation-side termination controls.
  They must not be treated as semantic equalities. In `ConstraintWeights`, they are named as termination guards and run only
  after W-Mix; they still need a separate worklist termination argument.

- Active-family extraction must use active stack pushes only. The old mixed `stack_items()` helper was removed to avoid
  accidentally treating floor as a visible push family.

- Any test expectation that removes a residual solely because the current implementation prints a simpler type is suspect.
  Principal residual surface is part of the theory.

## Implementation Slices

1. Add directed weight data structures behind the constraint machine.
   - `LeftStackWeightEntry { id, leading_pops, family, active_pushes }`
   - `LeftStackWeight`
   - `RightStackWeight`
   - `ConstraintWeights { left: LeftStackWeight, right: RightStackWeight }`
   - Unit tests for same-id composition, `take;pop` cancellation, `pop;take` preservation, and W-Mix projection.
   - Status: done with `LeftConstraintWeight` as the solver-facing left wrapper.

2. Port row upper handling to the directed contract.
   - Distribute right pop to the row tail.
   - Compute `J = K ∩ Common(left)`.
   - Hash-cons residuals by `(source, J, left_minus_J)`.
   - Keep self-tail no-op.
   - Status: done for `row_effect.rs` using a legacy `StackWeight` bridge.

3. Rework annotation translation.
   - Contravariant slots produce left `take(H)` weights.
   - Contravariant wildcard produces `take(All)`.
   - Covariant concrete annotations produce filter checks.
   - Fresh internal effect variables are protected with `take(Empty)`.

4. Rework bound replay.
   - Store full `(L, R)` in lower/upper bounds.
   - Compose by directed path composition.
   - Do not exchange unmatched right-pop with a new push.
   - Treat pop-growth caps as temporary termination guards only if they remain needed.
   - Status: mostly done. Replay now stores directed left weights and pure-pop right weights, runs W-Mix before
     explicitly named termination guards, and materializes left weights only at compact/generalize/test helper boundaries.

5. Rework compact extraction.
   - Positive projection keeps full left weight.
   - Negative projection keeps right pop only.
   - Filter is erased after checks.
   - Cleanup uses the colored sufficient condition: if a positive type has no active push for an id, pure pop for that id can be dropped.
   - Status: partial. Bound projection follows left/right polarity, and cleanup liveness now ignores legacy floor.

6. Audit family type arguments in effect-family set operations.
   - Same-path family intersections, subtraction, duplicate row heads, and filter comparisons must enqueue invariant
     argument constraints.
   - Status: mostly done in the constraint machine. Remaining risk is legacy `StackWeight` set operations outside
     machine-owned checks; these should not be treated as proof-carrying set operations without a machine context.

7. Audit runtime marker placement against the colored proof.
   - The proof assumes normalized marker materialization and well-bracketed color flow.
   - Existing active marker/hygiene runtime work should be checked against that invariant after inference weight semantics are fixed.
   - Status: in progress. `control-vm` and `mono-runtime` now paint both escaping request payloads and request
     continuations when a marker frame closes over a request, matching the `poppaint` rule for operation outcomes.
   - Guard coloring now uses a scope-entry except snapshot instead of the current visibility predicate.
     Each active add-id marker records the active frame prefix from the point where its frame was entered.
     A request is colored by that marker only when its existing guard ids do not intersect that prefix.
     This keeps an outer marker responsible for requests that are only hidden by later inner scopes, while avoiding
     repainting requests that were already excepted before an inner marker started.

## Regression Targets

Small tests should directly mirror the paper examples:

- protected row: `PWeight(take(Empty), alpha) <: [H; beta]` does not consume `H`.
- allowed subtraction: `PWeight(take(G), alpha) <: [H; beta]` consumes only `G ∩ H`.
- multiple active ids consume only `K ∩ G ∩ H`.
- right pop distributes through function domain by variance, not by moving arbitrarily across an edge.
- self-tail split does not create a fresh residual loop.
- filter erasure preserves a principal tail.
- `let rec` uses a single monomorphic root inside the RHS and only generalizes after the recursive graph is saturated.

## Do Not

- Do not add rigid/protected variable sets to stop simplification.
- Do not use path/name/test-specific branches in inference.
- Do not collapse `Any`, `Never`, and `Unknown`.
- Do not justify `pop(n) -> pop(1)` as a type equality without a separate termination theorem.
- Do not combine left and right weights before row split.
