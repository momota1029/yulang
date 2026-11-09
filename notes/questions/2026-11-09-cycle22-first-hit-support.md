# Cycle 22: first-hit is not settled source selection

No new language decision is requested here; defer full driver replacement until
candidate-guarded derivations are connected. The existing spec says to delay child
finalization until sibling updates stabilize. This note records the implementation
boundary, rather than inventing a first-match rule.

Illustrative Yulang declaration shapes (not parser/runtime tested):

```yulang
impl Parent (box int)
impl Parent (box 'a) where Child 'a
```

For an initially unknown payload, the literal inspection is deferred while the
capture inspection hits. `production` nevertheless chooses that hit and expands
Child. When the shared payload becomes int, the earlier literal also hits;
`production` changes to it and stops expanding Child. `frontier` is pending before,
ambiguous after, never selected. Lean proves both facts for a Paterson-checked
unary registry, and proves that actual recomputed Reach loses the child.
This is NOT a claim that Yulang permits picking either implementation.

Options for implementation work, without altering spec:
1. Defer the general B4 claim. Retain candidate guards and keep these speculative
   equations separate until the stable frontier is finalized. Recommended.
2. Attach provenance to equations and revalidate against final Reach. This cycle
   formalizes an observation view and executable unsupported-token audit, but it
   does not prove convergence after retracting stale equations.
3. Do not add unconditional EmissionMonotone. Ordinary atom inclusion is insufficient;
   monotonicity for the actual annotation adapter is exactly annotated Reach persistence.

The associated decoder counterexample is not constructed here: the verified loss
uses a real ordinary equality extension directly. Thus this does not by itself refute
EmissionMonotone specifically restricted to every associated-only decoder or every
legal history. It invalidates the proposed proof from atom inclusion alone.
