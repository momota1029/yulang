# C375: from an actual typed installation to its current release

I-65 step 1. This note composes existing C360 checks, independently
of the C374 declaration-ordinal bridge. It does not add a witness
shape or premise to the frozen soundness statement.

## The exact additional premise after a genuine event

Let `p : NativePreparation360.Prepared e frame d layout` and let
`a : NativeValue360.Compiled p table wire version` be the result of the
actual typed authoring route. Its stored `a.write`, by definition, has
the parent occurrence, declaration/version, authored declaration
ordinal, output and source-equation ordinals, and the fixed target
from that particular compiler argument. Its code is the actual
compiler's `emit` on the exact parent capture slots, not a code
inferred from a fitting value. This is still not a candidate election.

If `install p a base = some next`, then on the actual branch of
`install`, `next.board = add base a.write` and the existing Boolean
check yields `Committed base a.write`. Its active-owner, unique
active-position list, and fresh-target facts are therefore produced
by the install, not extra release assumptions. In that exact board
`authored_target_appears` gives
`atTarget next.board a.write.address.target = some a.write`.
The append leaves the active list unchanged. Thus:

> For any independent release gate, exact release of `a.write` on
> `next.board` exists **iff** its full `a.write.address` belongs
> to the gate's grants.

The forward implication is the `Released.granted` field. For the
reverse implication, unfold `checkExactRelease` then `openWrite`;
the actual stored row identity selects the correct lookup branch,
the install supplies active/unique, and the granted address supplies
the final guard. The same target with a different declaration
ordinal, source-equation ordinal, output ordinal, original occurrence
or version is **not** this release: even if it is granted independently,
`openWrite` compares the whole stored address and returns none.
This is a source argument about the existing checks, not an assertion
about how authority decides membership.

## Retention of that very event

For any finite sequence of later C360 board appends at different
targets, induction using `other_target_unchanged` preserves the
identical lookup; `add` keeps the active list. Therefore the same
iff applies to that final board with respect to *its* supplied grant
list. A later successful `install` on this already occupied target
is impossible on this append-only route by the freshness check.
A replace/delete API, refresh of active versions or grant withdrawal
is deliberately not treated as an append. If the active version or
grant is no longer current, the old literal installed row is not
sufficient to release it.

In one actual final fitting model, `checked_exact_written_value`
on the retained board now reads exactly `a.write.code.eval m`. In
the ordinary component, if independently derived C372 retained
prepared/where/fixed rows give a `Receipt` into this very final
ordinary state, `relays_models` gives their meaning in the **same**
assignment `m`; neither changes the state or invents a model to
cover gaps. The existing C360 `SequentialNative360.Sequence` is a
real instance of the ordinary-replay/unchanged-board case:
`Sequence.final` uses the continuation's ordinary stage and the
same `ordinaryChild.final.board` where the writer's exact release
was checked. Keep current body/capture, board slot, and gate as three
distinct sources. No equation in C372 supplies that grant.

The missing source-to-event portion is now explicit: actual
independent authorization of the selected occurrence (not equality of
declaration or ordinal), its starting allocator/capture layout, and
an applicable authored grant. Native event construction and earlier
K2/priority remain open. No general acceptance or reader completeness,
new fixture, or termination result is claimed. This note follows fixed
Lean sources and is not a new Lean execution.
