# F5c ordinary Function-ring complexity audit

Date: 2026-09-28
Scope: source-level accounting for the productive Function SCC ring in the
no-cap addendum
Reviews: architect/source audit, compiler referee, and performance audit;
read-only, no unresolved semantic issue or concrete counterexample

## Result

The current source does not yet certify the addendum's ordinary-ring target
`O(N² log N)`, where `N` is the number of definitions. This is an evidence
gap, not a demonstrated superquadratic behavior. The no-cap policy remains
authoritative; production cutover remains closed until the target's premises
are proved or a reviewed product tradeoff is selected.

The exact recipe produces `N` definition roots, `N` body-use rows, `N`
Function lower facts, and `N` internal uses. Each member has one distinct
guarded candidate owner. The predicate walk and that owner's lower-bound walk
can each record a guarded trace of `Θ(N)` hops, so the trace term is two long
traces per owner and `O(N²)` trace hops overall.

The remaining active-propagation term is not bounded tightly enough. Each
`enter_active` and `leave_active` event seeds memo incidence work and visits
reachable reverse-parent, root-edge, and conflict-update adjacency. The memo
persists between member drafts. Cyclic frames are tainted before summary
admission, but the inspected source does not establish a per-row bound on the
retained acyclic adjacency visited across all roots. For root `k`, let
`E_k(r)` be the adjacency work triggered by active event `r`; current source
supports only this accounting form:

```text
T_active = O(sum_k sum_{active events r in root k} (1 + E_k(r)))
```

The one-owner/two-trace result closes the trace-copy term; it does not bound
`E_k(r)` or the cumulative replay/output volume. `build_inner`, R filtering,
substitution, and flattening also lack a source-derived exact selected-node
census sufficient to establish `D = O(N²)`, descriptor width `W = O(D)`, and
the resulting height-group comparison bound for `Normalizer::rank_all`.

## Next proof gate

Establish the active memo edge cardinality and visit sum per root from the
exact ring's row and owner construction, then establish draft/output node
cardinality and descriptor width through replay, substitution, flattening,
and batch normalization. If any term exceeds the approved target, return to
the owning implementation or a reviewed product decision before production
cutover. The completed §15 source-ring capture budget is exhausted; any new
measurement requires a fresh reviewed plan and budget. No code, tests, builds,
or measurements were run for this audit.
