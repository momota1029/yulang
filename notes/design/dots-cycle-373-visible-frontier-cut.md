# C373: bind a retained event to the same visible frontier

I-65 step 1. This is a source-level composition from the published C367
and C372 cuts, not a new Lean run or a new candidate rule.

## Exact candidate identity across independent scans on the same state

Fix `s`, the complete current state, `q`, the same occurrence-indexed
request, and the model `m` already quantified in the frozen soundness
theorem. Suppose `Fits s m`. Let the independent source tapes `L` and
`R` both have type `CandidateTape s q (visible s q)`; their entries
need not be equal. Assume `TapedMatch s q L a` and
`TapedMatch s q R b`.

Then **a = b**. Otherwise `actual_matched_row` for the right tape gives
a genuinely stored `AuthoredCandidate s q b`; that candidate supplies
both `b ∈ visible s q` and a `SourceHead s q b`. Conversely
`rival_is_excluded_by_positive_evidence` for the left tape, with the
same `s,q,m` and `Fits` proof, rules out *any* `SourceHead s q b`,
not only ones already stored by the left tape. Contradiction. This uses
no new model-existence requirement in the soundness theorem and no
model extension. It does not establish fit-free determinacy of all
possible tapes; a `TapedMatch` still omits the additional native and
candidate-local K2 gate.

Within one tape the selected actual position is even simpler and needs
no model. An induction along `Stores` returns a matched ordinal:
the `here` case returns 0, and `later` increments the returned
ordinal, whether or not the preceding source row matched. A second
distinct matched ordinal would give two entries in `tape.live` (even
if the two source declaration values were equal); `tape.live = [row]`
rules it out. This is an ordinal of `visible s q`, not a global
declaration ID or a physical write address.

## What can be transported to a retained event

At each request occurrence one may reuse the declaration identity from
an independent event-side scan when it too is valid for exactly the
same `s,q`, not merely a pre-write state, a state with equal relevant
values, or another source occurrence with identical demand. In the
ordinary case if the event-side candidate is positively stored there,
and independently chosen by the full judgment, C372's actual
positioned retained rows plus prepared atoms/intervals supply
`BodyFacts` at that same state. Its `BodyLayout` is checked against
**that very event-side stored head**, not transported by equality of
the declaration. `authored_node` then assembles the local node without
rebuilding another capture or rerunning selection on the basis of body
success. The independent left tape can justify the same declaration
identity within the given model; it does not donate its captures or
body to the event-side proof.

This is narrower than uniqueness of the event or the output: two
scans with the same elected declaration do not, by this argument,
agree about actual origins, capture spans, literal placement, the
ordered children, or the fixed output trace. For these, match the
original event and its actual allocation/write positions as in C372;
do not substitute by declaration equality. Neither a stored match nor
this ordinary receipt witnesses the typed release or resolves earlier
native K2, and neither may be used to justify candidacy retroactively.

No change to classification or supported cases is proposed. This is
an identity bridge and an explicit boundary between model-free proof
production and equality inside the already quantified soundness model,
not a new condition on programs. No fixture was added, and I-65 step 1
is not yet closed.
