# Intrusion final-acceptance contract candidate

Date: 2026-09-30
Status: reviewed candidate formulation; not implementation authority
Scope: clarify the acceptance target after the user's priority decision
Governing sources: redesign charter; abstract-semantics draft; q-bound successor draft

## Candidate contract

The user has waived parity for inference-stage scheme formatting and the phase
at which a program is accepted. The final target is soundness and principality,
then the accepted-program capability of the completed pipeline. The abstract
semantics draft now records the following shape for a supported envelope `E`
declared independently of the successor implementation and its acceptance
result:

```text
soundness:     P ∈ E ∧ Accept_I(P)  => WellTyped(P)
completeness:  P ∈ E ∧ WellTyped(P) => Accept_I(P)
```

`WellTyped` must be an independent, syntax-directed declarative judgment, not
a restatement of either compiler's constraint generator or acceptance result.
The declared envelope may be built up in proof stages, but it cannot be
defined post hoc from the successor's accepted inputs or used to narrow the
full Oracle-capability objective. Any eventual resource limit must be stated
independently with its structural dimension, deterministic rejection point,
and failure behavior.

Principal-root semantics remains a separate obligation. For every admissible
fixed outer assignment `η`, each member's generalized root/use relation,
including declared subsumption, must equal the declarative source relation
obtained by projecting the joint satisfying relation onto that root and its
uses. This equality must include empty fibers and preserve shared outer
anchors; it cannot hold only after existentially choosing a favorable `η`.
Incoming uses must freshen owned identities independently while preserving
those anchors. Source constraint generation and its assignment relation must
first be shown adequate for the generalized component graph, including SCC
ownership and identity sharing. The final Oracle comparison
classifies any `Accept_O` / `WellTyped` disagreement using a concrete conflict
and the already recorded priority: reject Oracle-accepted ill-typed programs;
preserve acceptance for declaratively well-typed programs even when Oracle
rejects them. Inference-stage scheme text and phase-only differences are not
compatibility failures.

## Evidence and limits

The design draft and charter now state the soundness/completeness shape. The
q fixture supplies a concrete graph-level reason to retain a meaningful
one-polarity bound. Its Oracle `dump-poly` / `dump-mono` phase difference is
not a final-acceptance counterexample: both traced concrete uses fail
specialization. The full source constraint graph, `WellTyped` judgment, root
principality theorem, and declared envelope are not yet defined. No claim of
Oracle-capability equivalence or implementation readiness follows.

## Next proof gate

Define syntax-directed declarative source typing and constraint-generation
rules independently of both compiler implementations. First prove
assignment-relation adequacy between those source constraints and the retained
generalized component graph, including SCC ownership and shared identities.
Then prove exact root/use relation equality for every fixed outer assignment,
including subsumption, empty fibers, and retained meaningful one-polarity
bounds. The existing one-frozen-member theorem is a lemma in that chain, not a
substitute for graph/source adequacy or the full SCC theorem. Next add ordered
SCC preparation, publication, and incoming-use composition. Effects, roles,
and diagnostics remain outside the current pure graph theorem and need
separate extensions before the full Oracle-capability comparison can close.

## Review record

On 2026-09-30, compiler-referee and spec-auditor M3 reviews found no priority
or soundness-order contradiction. They identified and the primary addressed:
the missing source-constraint/component-graph adequacy step and explicit SCC
ownership; the need to quantify exact root/use relation equality over every
fixed outer assignment, including subsumption and empty fibers; independence
of the declared envelope from implementation acceptance; and the need to
define declarative constraints independently of either compiler. The reviews
did not certify the full semantics, Oracle envelope, effects, roles, diagnostics,
runtime soundness, or implementation readiness.
