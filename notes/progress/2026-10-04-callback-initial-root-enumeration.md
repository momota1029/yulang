# Callback B initial comparison-root enumeration

Date: 2026-10-04. Branch: `research/simple-sub-intrusion`.
Status: bounded conditional source-origin lemma; no source-rule change or
implementation authority.

## Result

For a fixed finite ordinary source derivation graph, let `k` be the number of
eligible callback-literal **derivation occurrences** in the bounded callback
contract: unannotated literals at known callees, with ordinary
`Value(F_cb)` formals, supplied instantiated callback interfaces,
slot/profile references, and completed literal interfaces. Normative B contributes exactly one initial
completed-interface comparison root per occurrence:

```text
b_i : F_lit,i <: F_cb,i
```

Each root retains its source occurrence and original lexical/context/profile
references. Count derivation occurrences, not printed literal text or distinct
endpoint pairs: shared syntax elaborated under two expected callback contexts
has two roots. Equal endpoints do not merge roots. For each admissible
endpoint substitution, consistent renaming transports the same indexed root
family while preserving typing premises, role/entry skeleton, and incidence.
This does not imply a finite union of endpoint terms across all substitutions.

Recursive references reuse registered source nodes, so execution revisiting a
node does not create another initial source root. This says nothing about
runtime activation or request histories.

Explicit annotations, annotation/callback overlap, unknown callees, retained
`Computation` formals, and scheme-instance generation remain outside this
lemma, as they are outside the bounded callback contract.

## Evidence and limits

The root count follows directly from the Authoritative callback contract
§§2–2.1: expected context selects Handler before body generation, endpoints
are independently synthesized, and the completed interface receives one
ordinary inequality. Core elaboration §6 supplies finite source-node identity,
recursive-reference reuse, and admissible transport conditions. The finite
context design remains Draft; its §4 annotation/check corollary is an analogy
for retaining root context, not the authority for this callback rule.

Independent compiler-referee and spec-auditor reviews were clean. Their scope
was this conditional initial-root lemma and its quantifiers. No tests, builds,
measurements, or Oracle inspection were run.

This result does **not** construct complete Function interfaces or scheme
instances, prove finite endpoint alphabets, conversions/adapters, source-wide
generation, derived-query/context closure, replay invalidation, method choice,
residual solving, principal solutions, or runtime bounds. In particular,
finite source roots do not establish finite derived-query contexts, and the
finite-context Draft's global closure theorem remains conditional and open.
The existing callback Function theorem and Milestone 3 blockers remain open.

## Governing sources

- [Authoritative callback contract](../design/2026-10-03-callback-context-delivery.md), §§2–2.1.
- [Draft finite-context closure](../design/2026-10-03-source-context-finite-closure.md), §§2–4, 6.
- [Draft typed-computation core elaboration](../design/2026-10-02-typed-computation-core-elaboration.md), §6.
