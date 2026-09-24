# F5c mixed-height normalization ordering addendum

Status: Authoritative for mixed-height normalized child order; implementation open\
Scope: The total canonical order used for normalized Union/Intersection children when their postorder heights differ.\
Approved-by: user, option B, 2026-09-24\
Review context: The prior architect/M3 review and handoff identified this exact conflict and presented both alternatives; the user selected B. No new independent review was run for this narrow selection under the user's primary-only direction.\
Supersedes: F5 §25's child-order rule only where it conflicts with §36's postorder-height ranking.

## Decision

Use §36's height-major descriptor ranking for every normalized child set. A
node at a lower postorder height sorts before a node at a higher postorder
height. At one height, sort descriptors by the specified stable top-down
mergesort and lexicographic descriptor-word order. Equal descriptors share one
rank; unequal descriptors receive consecutive ranks in that order. These
ranks alone determine normalized Union/Intersection child order and exact
duplicate removal.

This explicitly selects §36 height-major order over §25 structural-first
order for mixed-height children. At one fixed height, the §25 structural
comparison is expressed by the §36 descriptor-word comparison. Do not add a
second global structural rank that can interleave different heights.

## Preserved authority

- The 2026-09-23 producer-order addendum remains authoritative for first-
  surviving Q/R producer encounter, the pre-pruning polarity census, and
  post-Q/R normalization.
- F5 §36's `O(N + W + C)` normalization bound, deterministic mergesort,
  collision handling, counters, and resource ownership remain in force.
- F5 §44 remains unchanged: publish one source fact using the first member of
  the final normalized positive Union; keep all other members as private live
  constraints in the same transactional route operation. Because the order is
  now height-major, a mixed-height Union may select a different representative
  than structural-first ordering would have selected.
- No `yu-types` API, finalizer callback, live Union Term, or F5e public
  accessor is authorized by this ordering decision. The separate indexed-
  finalization API proposal remains unapproved.

## Implementation gate

Implement a bounded, stack-safe post-Q/R normalization pass that uses the
height-major total order and preserves descriptor deduplication. Carry the
required representation through the existing finalization boundary without
changing §24. If that cannot be done while preserving F5b accounting and
callback invariants, stop and return with the exact API/accounting choice
needed; do not approximate the order or weaken the resource bound.

Tests must include mixed-height positive Union and negative Intersection
children for which structural-first and height-major orders differ, verify the
height-major rank and duplicate behavior, and verify §44's public
representative is exactly the first member of the final normalized Union.
Stack-depth and checked-failure witnesses must cover the new pass. The
component-wide descriptor and scratch accounting must reconcile to §36 and
the existing F5b finalization checkpoint.
