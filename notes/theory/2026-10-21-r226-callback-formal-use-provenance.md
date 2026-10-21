# R226 — Callback formal-use provenance

Status: bounded metadata packet closed; typed provider/formal bridge remains OPEN.
Baseline: `9429c1fbb` on `research/simple-sub-intrusion`.
Parent computation-forwarding theorem, R71 and R72 remain OPEN.

## Result

R226 retained an occurrence-to-formal-registration index alongside candidate source calls. The existing candidate-context source origin already retains the branded `ConstraintOccurrenceId`, so the two owners now join through its exact `HirOccurrenceId` without copying a registration onto every relation or relying on solved row/term equality.

The index stores `(occurrence ordinal, one-based formal-registration index)` only for Apply calls whose callee has a registered formal name. It is sorted once after source collection and duplicate ordinals reject collection. Its compact vector capacity is included in `candidate_call::State::bytes`. The lookup also checks that the occurrence belongs to the same HIR artifact. The existing full `by_occurrence` map remains scoped to scoped-experiment mode.

The captured-graph byte assertion now enumerates the existing context-view, source-region, negative-function, capture-frontier, and forest buffers as well as its node/row/bound arrays, so it checks the complete graph accounting formula.

## Exact R221 source evidence

Focused test: `r226_callback_formal_use_origin` in `crates/yu-solver/src/candidate_scheme.rs`. It runs ordinary candidate mode with the exact R221 source and no scoped experiment.

- The callback-body Apply at occurrence 19 has source-origin relation 146. Its `Origin` retains occurrence 19; the compact source index resolves that occurrence to the same registration referenced by the call's `formal_name`.
- The resolved source name is the callback parameter `f`; the candidate call's `formal_registration` is the registration used for this exact source name.
- Provider Apply `repeat loop` at occurrence 26 has relation 357. Its call has no `formal_name`, and the compact index returns no formal registration.
- R225's provider relation path remains present: the provider Apply argument comparison reaches actual route Term 413 versus expected callback function Term 377, and its result-effect child is relation 368 (`EffectRow(69) <= EffectRow(54)`).

This closes the source-identity lookup seam identified by R225. The provider expected function Term 377 still has no established typed route to callback WorkBound demand Term 340. Relation 146 still has no FunctionPort dependency. The metadata does not prove a LocalFreshRoute-to-formal typed transformation or later production `Work::Bound` consumer.

## Scope and follow-up

No inference relation, term-solver rule, public API, language behavior, or theorem premise changed. This is source provenance only. R71, R72, and the parent theorem remain OPEN.

The next proof step should consume the exact registration index to construct an owner-qualified formal-route join, then prove the resulting typed comparison against the original obligation. A counterexample is any ordinary candidate source where two distinct branded HIR occurrences resolve to the same ordinal within one batch, or where the compact index resolves an Apply occurrence to a formal registration different from the source call's validated `formal_name`. The collection seal rejects duplicate ordinals, and the focused test checks the exact callback and provider cases.
