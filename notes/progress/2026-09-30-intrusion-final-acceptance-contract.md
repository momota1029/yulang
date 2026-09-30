# Intrusion final-acceptance contract candidate

Date: 2026-09-30
Status: candidate formulation; unreviewed; not implementation authority
Scope: clarify the acceptance target after the user's priority decision
Governing sources: redesign charter; abstract-semantics draft; q-bound successor draft

## Candidate contract

The user has waived parity for inference-stage scheme formatting and the phase
at which a program is accepted. The final target is soundness and principality,
then the accepted-program capability of the completed pipeline. The abstract
semantics draft now records the following shape for a supported envelope `E`:

```text
soundness:     P ∈ E ∧ Accept_I(P)  => WellTyped(P)
completeness:  P ∈ E ∧ WellTyped(P) => Accept_I(P)
```

`WellTyped` must be an independent declarative judgment, not a restatement of
the implementation's acceptance result. Principal-root semantics remains a
separate obligation: for each member and fixed outer environment, the
generalized root must denote exactly the admissible source substitutions,
with independent freshening at incoming uses. The final Oracle comparison
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

Define the declarative source typing judgment from source-generated constraints
and their effects, independent of inference acceptance. Then prove the root
denotation/principality theorem for one frozen member over a fixed outer
environment, including retained one-polarity bounds. Only after this local
theorem holds should the proof add ordered SCC preparation, publication, and
incoming-use composition. Effects, roles, and diagnostics remain outside the
current pure graph theorem and need separate extensions before the envelope
can claim those features.
