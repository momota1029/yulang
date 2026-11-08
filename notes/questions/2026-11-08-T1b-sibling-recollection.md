# T1b: state-changing siblings and recollection order

Status: open; no language-semantics choice made. 2026-11-08.

For an open role interval, a child can add ordinary constraints that invalidate
an earlier sibling's current candidate. For example, schematically:

```yulang
impl Parent (box 'a) where Left 'a, Right 'a
```

Suppose Left currently has two possible implementations while Right narrows
`'a` enough to leave only one. Reporting Left's initial ambiguity before
propagating Right differs from recollecting Left afterward. The present
fixed-frontier outer resolver does not specify a state-returning child protocol.

Options (deferred policy first):

1. Keep the parent and ambiguous child deferred until state propagation reaches
   a stable point; regenerate every sibling and the parent after updates.
2. Traverse source-order children, retain all updates, then repeat the complete
   sibling scan until the state/obligations stabilize; intermediate outcomes
   are not final language errors.
3. Another owner-specified saturation protocol with a precise finalization
   criterion and declaration-derived termination measure.

The implementation in this task may record ordered passes and final-state
regeneration, but does not choose when an intermediate ambiguous/pending result
becomes a final error. Reordering a *fixed* conjunction is semantically neutral;
this alone does not establish order independence of a state-dependent producer.
