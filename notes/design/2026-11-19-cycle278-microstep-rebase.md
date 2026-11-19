# Cycle 278: microstep-semantic rebase of the checked 239 and 240 loops

Cycle 259 checks full models at round boundaries and a report-driven finite
write. It does not relate the actual states *inside* each raw round. The
present target is the actual install, refresh, and reobserve microstates,
including where the fresh upper name first becomes constrained.

Use a three-phase source presentation (enter / installed / refreshed), with
reobserve crossing into the next round, and the existing normalized
write as successor. The same explicit source-boundary-preserving assignment
must satisfy all intermediate old states as well as the new state. Every
old microedge either lifts to the unique new write or has literally the same
normalized state and no corresponding new write. Check this on both fixtures;
the old raw infinite paths remain real. Arbitrary old branches, the complete
source compiler, and arbitrary-state termination are outside this boundary.

## Executable rebasing of encoded old names

The existing 240 uniform reconstruction searches all indices up to the
numeric name. Allocation codes are iterated pairings and are very large
even at low ranks. Implement a checked inverse of the square-band pairing,
then extract the encoded predecessor. Validate the entire expected slot by
re-encoding it, and descend only to a strictly smaller predecessor. A
left-inverse proof on authentic allocations and a right-inverse check on
arbitrary names are both required. On the two loop families, a successful
decode returns the exact old stage and polarity. On 240 the replacement
lookup must agree pointwise with the old bounded-scan reconstruction.
No general compiler, changed language meaning, or quantified bit-complexity
bound is asserted by this isolated replacement.

## Two separate clocks, with exact history comparison

The full old model sets, not just their public projections, form a strict
reverse chain indexed by the number of actual installations. To prove that
the implication cannot hold in the other direction, take the explicit
upper-bottom complete assignment indexed by the smaller counter. The
tracked positive Known observations are a different increasing chain,
indexed by the number of refreshes. An executable comparison of the two
counters is exact for the conjunction of these two comparisons on either
fixture. The pair of counters identifies a tick except that reobserve connects
a refreshed tick to the next enter tick with the same pair. This is **not**
a transition key: those equal-key ticks admit different next operations and
do not have the same install availability. Public assignment preservation,
V8 leaf readback and one-write normalization are proved separately.

The exact full old predicate can also be unfolded into the initial predicate
and the finite prefix of actual Holds obligations. It never eventually
stabilizes on either path. The semantic counters with **one additional bit**
for raw install availability recover the displayed tick injectively. The
checked decoder rejects inconsistent keys; every executable key advance is
an actual edge in both displayed fixtures (a mixed 239 edge and a point
240 edge). This is an executable representation of those paths, not an
enumeration of every branch in the general raw operational semantics.
