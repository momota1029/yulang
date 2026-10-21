# R216 — Capture reverse-owner bound readback

## Decision

R215 correctly established that `Effect(10)` is not in
`effect_bounds[31].direct_lower_rows`, but the conclusion that the relation was
missing before bound storage was too strong. The same filtered local-source
test output records source relation 71, `Effect(10) <= Effect(31)`, as admission
64 and physical emission 61 at `Effect(10)`'s `EffectUpperRow` slot 0. Physical
readback returns the same bound. The source relation is present in solver bound
storage, on the lower endpoint's upper-bound lane.

`candidate_apply_effect` selects `(owner=Effect(10), polarity=Negative)` for
this equal-level pair. `candidate_insert_bound_with_evidence` writes a negative
row bound to `effect_bounds[10].direct_upper_rows`. The R215 snapshot queried
the opposite representation, `effect_bounds[31].direct_lower_rows`, which
therefore contained only `[28]`.

## Capture consequence

`Capture::expand_row` expands direct lower and upper rows owned by the row it
has already visited. It has no incoming-owner index that finds Effect(10) when
walking from Effect(31), even though Effect(10)'s upper list points to 31. The
route graph consequently omits relation 71 because its owner row is outside the
visited frontier. The candidate-level root cause is asymmetric frontier
discovery under one-sided bound storage.

This corrects R215's interpretation without changing its recorded snapshot.
It remains a candidate implementation finding for one fixture. The original
forwarding-preservation theorem, its source/native bridge, independent review,
semantic approval and production gates remain OPEN.

## Evidence

- Filtered `local_source_observation --nocapture`: relation 71's admission,
  physical slot and readback; Capture snapshot `[28]`; route bounds omit 71.
- `candidate_apply_effect` in `candidate_extrusion.rs`: equal row levels select
  the lower row as a negative upper-bound owner.
- `candidate_insert_bound_with_evidence`: negative effect-row bounds are stored
  in `direct_upper_rows`.
- `Capture::expand_row` in `candidate_scheme.rs`: only expands bounds owned by
  the currently visited row; it has no reverse-owner query.
