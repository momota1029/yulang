# C372: retained literal body — source event, layout, ordinary relay

I-65 step 1 only. This cut elaborates the retained-write premise of the
existing ordinary body, not a classification rule or a new input-admission
test. It uses checked Lean source pinned before C372; the construction
below is a source-level argument, not a fresh Lean run.

## A real literal suffix, and what it buys

`GeneralDeclarativeWitnessCompiler350.execute` actually runs preparation
to obtain `(prepared, ports)`, obtains the source-ordered `whereRows` from
`whereBatch` and root `fixed` rows from `fixedBatch`, and constructs the
literal children with exactly `placed c ports`. `Finished.state` applies
`appendFacts` twice, which changes only `equations` and concatenates on
the right. Thus on that run, writing `p = prepared.equations.length` and
`w = whereRows.length`, the two exact disjoint intervals are:

- generated where row `j` is at `p + j` for `j < w`;
- fixed root output row `k` is at `p + w + k` for `k < fixed.length`.

The second equality holds with subsequent appends as well, without
putting those appends into the finished body. The corresponding current
equation is literally the complete emitted equation (including the
computed RHS), not just a row with the same target, a logical alias, or
an equality having the same value in a model. The equality is a simple
pair of append/index calculations. `fixed_targets` identifies the fixed
left-hand targets in root demand order. The children instead come from
the same literal `placed c ports`, not from re-evaluating the fixed rows.

A sufficient **source-event route** for the ordinary selected slice is:
use the independently selected authored row and authorized allocation
for this occurrence; compute preparation, where batch, fixed batch,
and children; then take a retained ordinary compilation event anchored
to that occurrence and placement. In the append case, its prepared
equation prefix and the next two exact batches form a prefix of the
actual current `s.current.ordinary.equations`. A more permissive
retention format may carry an order-preserving index map for the
produced rows, but that format must be tied to the event, not found by
searching for model-equal equations. A visible pair of matching rows
does not create an event, a parent occurrence, or a release.

## Bridge into existing evidence rather than another receipt premise

From the literal current prefix, `Finished.state.equations ⊆
s.current.ordinary.equations`. If the prepared ordinary atoms and
intervals are also retained in this same state, the two unchanged
normal parts and the equation inclusion are precisely the three fields
of existing `GeneralDeclarativeGrowth327.Extends`; use
`GeneralDeclarativeCurrentReceipt330.literal` to get the current
`Receipt`. Hence the same run supplies `WrittenBody` at the exact
`Current`, and then `BodyFacts` with positioned children
`children q f.kids`, without a pre-supplied Wire, a model choice,
or a second decision on the candidate. `BodyLayout` remains a
separate selected capture-to-compiler input fact.

A discrete clock or serialization is not required for the soundness
of `Receipt`. If a finite ordered receipt is needed later, the actual
absolute positions may be replayed with C349's `Code.currentRow`;
compile-time slot roles keep where and fixed disjoint, even with
identical equation values. C349 `verify` alone allows reusable current
rows and arbitrary ordinary derivations: it proves same-model relay,
not that a particular occurrence produced a literal block. Conversely,
no need to strengthen semantic same-model relay to require a
contiguous block where authorized provenance is represented differently.

## Actual remaining producer

Neither the current ordinary equation list nor `Fits` contains a
source occurrence index, allocation authorization or production-event
identity. `FrameReadback325.Recorded.written` proves membership of a
compiled root batch but not the generating event or its absolute
positions. `WrittenBody.retained` is also semantic. Only their
mathematical consequences may be reused; none authenticates, for
example, two source events with the same equation value. Current
physical typed `ExactRelease` is a separate notion and is not given
by this ordinary append argument.

Consequently the exact implication left to prove for frozen step 1:
the independently allowed, actually selected source frontier must
produce the occurrence-keyed retained ordinary event/layout (or its
source-justified ordered position map), corresponding typed-write
authoring, and recursive child selection. The above sufficient
retention route neither claims this producer nor demands a new
language-side receipt from programs. It is not the old solver
projection, a completeness/termination statement, or an extension of
candidate acceptance. No fixture was added.
