# Mixed scalar and callable callback-result projection probe

Date: 2026-10-05
Status: finite characterization; no theorem, production denotation, or implementation authority
Governing direction: [inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md), the [source-indexed callback realization](../design/2026-10-04-source-indexed-callback-realization.md), and [certified callback transport](../design/2026-10-04-certified-callback-and-constrained-use.md)
Review: compiler_referee reviewed the initial checker, found a major fixed-challenge violation in its mutant, then reviewed the repaired checker; no remaining blocking or major finding in the revised bounded scope

[`tools/research_callback_nested_value_projection.py`](../../tools/research_callback_nested_value_projection.py)
combines the scalar widening from the `Sat_j` probe with the retained callable
identity from the higher-order projection probe. The finite source relation has
two correlated package inputs:

```text
(0, callable-left)
(1, callable-right)
```

Identity returns the complete package. A later client invokes the returned
callable with the returned scalar; the request family is `Read` for scalar `0`
and `Write` for scalar `1`. Both providers have the same declared Function
interface, with both request families in its effect row. The observation
retains the original challenge, typed paths, request family/origin/event, and
continuation owner. The typed projection erases scalar payload fields but
keeps later event evidence that can depend on those coordinates.

The checker exhausts both source challenges. Ground-only saturation widens
the returned scalar to either `0` or `1`, while holding the original input
tuple and callable owner fixed. Both source observations remain in the checked
projection (`2/2`), but equality fails: for input `(0, callable-left)`, the
extra result `(1, callable-left)` makes the later call emit `Write`, whereas
the source identity observation emits `Read`. There are two such extra scalar
observations across the finite domain. This shows that an inert ground value
can become observable after a retained dependent consumer; local scalar
erasure does not establish equality after arbitrary result composition.

A whole-package mutant also varies the result callable owner under the same
fixed challenge. It adds four observations; the minimum is input
`(0, callable-left)`, result `(0, callable-right)`, with the later request
origin owned by `callable-right`. This separately confirms that same-interface
callable substitution changes future typed evidence. It does not show that
the ground-only widening violates the one-sided source-inclusion condition.

The total-coordinate check adds coordinates as functions of the complete old
observation and erases them back to the exact saturated relation. It checks
only this finite construction. A first checker draft accidentally built the
mutant result by calling the source relation for a different package, thereby
changing the challenge as well as the result. Compiler-referee review rejected
that false witness; the final checker now fixes the challenge in every
candidate result and asserts the input-owner field is unchanged.

The new characterization is the mixed dependent-consumer case: the previous
scalar checker did not return a callable package, and the previous callable
checker had no scalar whose later consumption selected an observable request.
The package is an ordinary finite record in this model; no existential binder,
existential elimination rule, or hidden type witness is modeled. The
`arg-*` labels are redundant with the `Read`/`Write` family in this two-value
finite domain and add no independent claim.

This is not a production Function-bound rule or a counterexample to Theorem C.
It does not establish which widened observations are admitted by production,
how callback result consumers are generated, or what the complete inequality
solver accepts. It uses one fixed fiber, two package inputs, and one later
invocation; handlers, suspension/resumption, arbitrary histories, binder
hiding, general package types, and the full `nu,K,D` laws are omitted. The
result is evidence that any proof of exact projected equality across a
dependent future consumer needs to retain the scalar/callable relation or
account for the changed event. The existing one-sided inclusion and full
production membership obligations remain unchanged.

Verification:

```text
python3 tools/research_callback_nested_value_projection.py
  pass: 2 correlated package challenges
  pass: source typed projection included in ground-only checked projection, 2/2
  pass: total-coordinate extension erases to the exact checked relation
  minimized: fixed (0, callable-left), widened scalar 1 changes Read to Write
  minimized: fixed (0, callable-left), owner swap to callable-right changes request origin
python3 -m py_compile tools/research_callback_nested_value_projection.py
  pass
git diff --check
  pass
```

The production actual/checked membership rule and complete containment proof
remain open; this probe does not alter their gate.
