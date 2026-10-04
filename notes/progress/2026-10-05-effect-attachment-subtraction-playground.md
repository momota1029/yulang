# Effect support and attached subtraction: finite separation probe

Date: 2026-10-05
Status: bounded exploratory model; no annotation membership or handler rule selected
Scope: distinguish row support projection from event-specific partial subtraction
Branch: `research/simple-sub-intrusion`
Governing sources: [approved mixed-row handoff](../../questions/2026-10-05-function-effect-row-denotation/receipt.md), [concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md) §§6–9, and [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md)

## Refinement of the earlier candidate comparison

The [membership probe](2026-10-05-effect-component-membership-playground.md)
compared complete-port coverage with filtering an entire observation by the
row item's source occurrence. That distinguishes two predicates, but it
conflates row support membership with the evidence that licenses subtraction.
The user's partial reverse-addition clarification already requires the
corresponding concrete contribution and its attachment to be known. That
attachment selects which contribution may be reversed; it need not erase
another event with the same family point from the complete output support.

This follow-up keeps the layer distinction explicit:

```text
support point       = (effect family, concrete type arguments)
source contribution = one event/path with its own origin and identity
subtraction witness = attachment of that contribution to the concrete row item
```

It does not decide the still-open annotation-to-component membership rule.

## Finite model

[`research_effect_attachment_subtraction.py`](../../tools/research_effect_attachment_subtraction.py)
enumerates 256 pairs of events. Each pair remains in one fixed `(nu,K,D)`
fiber. The model keeps family/type support, event identity, origin,
contribution attachment, handler consumption, and complete-output reachability
as separate coordinates. Public support is a set, so duplicate event points
do not create row multiplicity.

The support projection can remove `write int` only when no `write int` event
remains in the complete output image. In 12 generated histories, an attached
and consumed `write int` event coexists with another output `write int`; a
targeted subtraction is witnessed, but deleting the entire support point
would be unsound. The minimized witness has `q0` attached and consumed and a
distinct `q1` from another origin reaching output. The projected row still
contains one `write int` point.

The run also checks 9 histories with multiple same-point output events:
event multiplicity stays in the retained evidence while row support contains
the point once. These counts characterize only the enumerated two-event model.

## Limits and next gate

The model assumes the attachment, consumption, and complete-output flags; it
does not derive them from `Flow`, `Observe`, handler activation, source
annotation elaboration, or production Function endpoints. It does not define
general family variance or a subtraction algebra. The support-level condition
is a finite projection check, not a theorem of source adequacy or principality.

The previous binary question about whether row membership itself must be
filtered to annotation-owned events is withdrawn as too coarse: source
membership, contribution attachment, and complete-image subtraction are
separate proof obligations. The remaining gate is to derive their connections
from source rules, using existing occurrence/path/attachment evidence, without
equating family support with event identity. No new carrier is proposed.

Verification: `python3 tools/research_effect_attachment_subtraction.py` and
`git diff --check` passed. No compiler tests, builds, or production changes
were made.

## Differential shallow-transition check

The checker now imports the separate bounded shallow-resumption model and
compares the event projection against its result for the same 96 fixed
histories. All event IDs, origins, family labels, selected-first handling,
one raw resumption, and terminal outer-family filters agree. This is a
differential consistency check between two research models with shared
assumptions; it is not an independent derivation of the source-machine rule.

Verification: `python3 tools/research_effect_attachment_subtraction.py`
reports 256 attachment/output combinations and 96 matching shallow histories;
the component-membership probe still reports 31 same-fiber subsets and 8
candidate-reading distinctions. No new semantic choice or production change
follows.
