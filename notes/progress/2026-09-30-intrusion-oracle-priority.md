# Oracle compatibility priority and divergence gate

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Status: research decision recorded; successor semantics not approved

## Priority

The current objective orders semantic qualities as follows:

1. soundness;
2. principality;
3. Oracle-compatible observable behavior.

Oracle behavior remains the reference target where it is sound and principal.
An observed mismatch alone does not justify divergence. Before selecting a
divergence, the record must include (a) a concrete counterexample or explicit
constraint conflict, (b) the precise Oracle behavior being dropped, (c) the
replacement rule and its soundness/principality rationale, and (d) the source
compatibility impact. A proposed replacement remains non-authoritative until
independent review and user approval.

## Current q-erasure evidence does not yet meet the divergence gate

Frozen Oracle `a58eefc31` infers an `any`-like argument view for
`pub f x = x f`; the inference-stage two-use characterization is recorded in
`notes/progress/2026-09-30-intrusion-q-finalized-use-path.md`. But the concrete
source `pub f x = x f; pub main = f 1` fails in `dump-mono` with
`int <: Function`. A temporary trace in the disposable frozen-Oracle checkout
records the queued and solved `f` instance as `Fun(int, [], [], unit)`; its
body check fails with that constraint. This resolves the exact instance
signature. The exported inference view alone is insufficient evidence that
Oracle accepts an unsound concrete use: downstream specialization preserves
the recursive constraint for this use.

Separately, the bounded-negative counterexample in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`
shows that polarity-only replacement of a constrained negative variable by
`Top` can change the candidate denotation. It is not the traced q graph and is
not evidence that Oracle makes that replacement for the same selected graph;
the observed `expect` fixture instead expands the negative variable to `Int`.
The graph-level counterexample therefore does not currently establish a
soundness/principality conflict with Oracle.

## Decision for the current gate

No Oracle behavior is dropped by this record. Do not encode q erasure as an
unconditional candidate rule, and do not claim the Oracle is unsound from the
inference-stage scheme shape. The next proof must relate the selected q-bound
graph and Oracle's per-use specialization recheck to the candidate's
generalization/instantiation semantics. If that proof finds an actual
conflict, write the four divergence items above before choosing the successor
rule. Until then the successor contract remains unresolved and implementation
remains gated.

## Compatibility impact if a conflict is later proven

No present compatibility change is authorized. Any later rule that preserves
the q bound in the public inference view or rejects the use earlier could
change exported scheme formatting, acceptance stage, diagnostics, or
provenance even if final program acceptance remains the same. These are
observable compatibility dimensions and must be measured and recorded against
the frozen Oracle before the successor is approved.
