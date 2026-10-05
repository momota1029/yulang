# Protection-only filtering over existing callback witnesses

Date: 2026-10-05
Status: conditional semantic derivation and finite characterization; no source, grammar, solver, or implementation authority
Governing decisions: corrected user meaning of `'e?`; callback protection and visibility equations in typed-boundary realization §6
Review: compiler_referee clean on the first conditional-filter packet; architect found that a single static `Γ_b(p)` bit cannot distinguish aliased routes
Probe: [`research_handler_protection_filter.py`](../../tools/research_handler_protection_filter.py)

## Conditional derivation

The typed-boundary candidate already defines an `Inc_C` witness as a join of
`Path`, handler/owner activity, and receiver activity. It defines protection
and capture grant separately:

```text
Protected(q,h,C) iff ∃w ∈ Inc_C(q,h). true
Grant(q,h,C) iff ∃w ∈ Inc_C(q,h). LocalOwner(w) ∧ ExplicitlyAdmits(w,q)
Visible(q,h,C) iff Active(h,C) ∧ Active(owner(h),C) ∧ Covers(h,q)
                       ∧ (¬Protected(q,h,C) ∨ Grant(q,h,C))
```

Let `w` denote a full typed `Flow`/`Observe`/`Receive` derivation witness, not
only the projected tuple `(q,h,b,p,C)`. Let `Release_s(q,w,C)` select exactly
the existing protection witness whose protection has ended as an already
`'e`-attributed contribution leaves marked slot `s`. It is a proof-side
premise in this derivation, not a new stored carrier. Then the local reading
of `'e?` can be expressed by changing only the protection query:

```text
Protected?(q,h,C) iff
  ∃w ∈ Inc_C(q,h). ¬Release_s(q,w,C)

Grant?(q,h,C) := Grant(q,h,C)

Visible?(q,h,C) iff Active(h,C) ∧ Active(owner(h),C) ∧ Covers(h,q)
                        ∧ (¬Protected?(q,h,C) ∨ Grant(q,h,C))
```

The raw `Inc_C`, `Path`, `χ`, event/provenance identity, family and arguments,
row support, typed paths, `K,D`, and any request witness remain unchanged.
If every applicable protection witness is released, protection no longer
blocks an active handler that covers the operation; ordinary ordered search
decides whether it is selected. If another independent protection remains,
the existing grant rule still applies. Release neither creates a grant nor
selects a handler.

Filtering released witnesses out of `Inc_C` before calculating both
`Protected` and `Grant` is incorrect. A marked receiver-local witness may carry
an explicit grant while an independent inherited witness still protects the
same request. Removing the first witness from both queries loses the grant and
incorrectly blocks the second witness, contrary to a protection-only change
and the existing no-origin-veto rule. `Inc_C` must remain intact for the grant
calculation.

The route-crossing probe demonstrated a possible way to compute `Release_s`
from typed evidence, but it did not establish that mapping as source semantics.
The projected `Path(q,u,b,p)`/`Inc_C(q,h,b,p)` tuples existentially hide the
intermediate Flow/Observe/Receive route. Selection must therefore occur over
the underlying derivation witnesses before those existentials are collapsed,
unless the release predicate is proved to factor through the projected tuple.
The source-realization candidate already describes worklist queries over each
actual path witness; this offers an implementation route over existing edges,
but source-to-query adequacy for released witnesses remains open.

## Exact remaining premise

The typed-boundary draft says that `Γ_b` records protected positions and
concrete contracts, but its displayed `Protected` equation treats every
`Inc_C` witness as protective. A single static `Γ_b(p)` bit is not enough to
implement route-local release: one protected view rooted at the same `(b,p)`
may reach two live alias views, only one through marked slot `s`. Toggling the
bit globally changes both paths; deleting `χ` or `Inc_C` loses the retained
provenance or a grant. The minimized case is exercised by the probe.

The exact missing premise is now narrower: a source rule must identify the
full existing path witness on which the marked slot releases that witness's
protection, and define the search point/lifetime where this applies. It must
leave sibling paths and every other protection witness untouched. This may
be computed from tagged existing Flow/Observe/Receive derivations before
projection; current documents do not prove those derivations distinguish all
required cases or that the marked slot is source-generated there.

Neither path crossing, event identity, lineage, family support, subtraction,
nor handler ownership supplies this rule by itself. The previous route-crossing
probe remains a candidate query characterization only. Nested/shallow/deep
handlers, resumptions and higher-order latent results need to satisfy the same
source predicate; they do not justify deriving it from a path heuristic.

## Finite characterization

The new checker enumerates 4,096 combinations of three supplied incidence
witnesses and handler/owner/coverage activity. It checks the conditional
visibility equation, that changing release status leaves grants invariant,
and that all-released protection returns the query to ordinary eligibility.
It also checks the minimized overlap counterexample to deleting released
incidences from both protection and grant, and the aliased-route counterexample
to one global `Γ_b(p)` bit: two derivations with the same projected tuple can
have different release status.

This is algebraic characterization of the conditional filter, not proof that
Yulang source constructs `Release_s`, not a source-to-endpoint theorem, and not
evidence that `Inc_C` itself is implemented in production. No new carrier or
production authority follows.

Verification:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/research_handler_protection_filter.py
  pass: 4,096 finite witness/activity combinations; grant and aliased-route mutants rejected
git diff --check
  pass
```
