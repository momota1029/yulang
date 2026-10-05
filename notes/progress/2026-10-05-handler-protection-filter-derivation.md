# Protection-only filtering over existing callback witnesses

Date: 2026-10-05
Status: conditional semantic derivation and finite characterization; no source, grammar, solver, or implementation authority
Governing decisions: corrected user meaning of `'e?`; callback protection and visibility equations in typed-boundary realization §6
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

Let `Release_s(q,w,C)` be a source-supplied predicate selecting exactly an
existing protection witness whose protection has ended as a contribution
already attributed to `'e` leaves marked slot `s`. It is a proof-side premise
in this derivation, not a new stored carrier. Then the local reading of `'e?`
can be expressed by changing only the protection query:

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

`Path` is currently an existential relation. If `Release_s` factors through
the projected tuple `(q,h,b,p,C)`, the filter can use that tuple. If selecting
release depends on which typed Flow/Observe/Receive derivation witnesses the
tuple, evaluate the predicate over those existing proof witnesses before
existential projection; do not erase all paths when only one qualifies. This
does not require a persistent provenance ledger, but source rules must retain
or reconstruct the derivation evidence needed by the query.

## Exact remaining premise

The source packages define how profiles move and when a handler/receiver
activation expires. They do not define a source rule that selects the
protection witnesses belonging to a marked output slot and says exactly when
that protection ends while the receiver remains active. That one
slot-indexed release/lifetime rule is the missing premise. It must preserve
all nonselected protection witnesses and keep every raw transport and event
fact intact.

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
incidences from both protection and grant, and a duplicate projected tuple
whose two derivations have different release status.

This is algebraic characterization of the conditional filter, not proof that
Yulang source constructs `Release_s`, not a source-to-endpoint theorem, and not
evidence that `Inc_C` itself is implemented in production. No new carrier or
production authority follows.

Verification:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/research_handler_protection_filter.py
  pass: 4,096 finite witness/activity combinations; grant-preservation and overlap checks
git diff --check
  pass
```
