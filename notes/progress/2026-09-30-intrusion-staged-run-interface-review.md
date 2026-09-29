# Intrusion staged run interface review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Scope: candidate Lower/Infer/Spec/Observe relation for the full source envelope
Status: reviewed interface; semantic rules and parity theorem remain open

## Interface added

The abstract-semantics draft now gives candidate signatures for
`Lower_X -> Infer_X -> Spec_X -> Observe_X`. Lowering returns constraints, a
machine-local-to-source map, and initial errors. Inference returns either a
ready state with ordered saved views and an identity-bearing proof ledger, or
a terminal outcome with its trace. Specialization is called only on the ready
path and likewise distinguishes completion from rejection. Observation gets
the initial errors, source map, actual phase traces, and tagged outcome so it
can compare public status, ordered diagnostics, and exported types.

The interface distinguishes handled fallback from terminal inference stop,
keeps the ledger from being mistaken for Oracle-emitted records, places
finalization/publication inside inference, and requires the trace to retain the
Oracle-related order of root collection, slot insertion, finalization, and the
all-member visibility barrier. The signature does not choose an intra-barrier
write order. Tuple arity and record-shape checks are deferred; nominal path
differences keep their `NominalCastNeeded` route; weighted effect-row
residuals remain in inference state/evidence.

## Independent review and repair

An architect review found that the first signature had no source-map consumer,
made every inference run appear successful, and did not model the publication
barrier. The draft was revised to thread `M_X`, add tagged `InferReady` /
`InferStopped` and `SpecDone` / `SpecStopped` outcomes, and record publication
order as trace. A spec-auditor review independently caught that specialization
must not run after terminal inference failure. Both reviewers confirmed the
case split and outcome model. A second narrow review confirmed that
`SpecDone` means successful specialization and the trace preserves root
collection, slot insertion, and finalization ordering without imposing an
unsupported write order.

## Remaining work

This is an interface, not an operational definition. The event tags and
payloads, weighted effect-row semantics, specialization judgment, public type
normalizer, diagnostic exposure, one-root simulation, source lowering, and
soundness/principality proof remain open. It does not select a new API or
authorize implementation. The full Oracle-capability objective remains
unchanged.

`git diff --check` passed. No compiler code, tests, Python, or measurements
were changed or run.
