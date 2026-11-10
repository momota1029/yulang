# Cycle99: ordinary evidence closure drives checked replay

Status: Draft, implementation theorem boundary. 2026-11-10.

## Goal and governing source

Connect the existing executable scalar evidence closure to cycle98's real
ordinary consistency gate and cached frontier replay. This removes the external
finite batch list for this concrete fragment, rather than introducing another
generic caller-provided job graph. spec/06-roles.md 6.3 permits information flow
through equalities and delays final role decisions until siblings are stable.
No unique-implementation hypothesis may create ordinary equalities.

Before implementation, read work/dots-audit x-oracle X13-X16. These are the
existing shared-box/depth/local-interval observations, not general evidence
scheduler evidence. No new Yulang2 run or semantic decision is planned.

## Data, independent judgement, execution and statements

Input: existing grammar-certified State n, finite slots Fin n. Reuse
CommonRoleEvidenceSaturation.Derived, whose constructors are explicit paired
scalar equality seeds and reciprocal variable-edge transfer. This is narrower
than arbitrary ordinary entailment. The four scalar bases are existing syntax.

Execution: compute saturate s over the internally enumerated Fin n × Base;
map each distinct result to the existing grammar-certified equality constructor;
feed those batches into CommonRoleCheckedOrdinaryReplay. The caller supplies no
batches, trace, fuel, model, Chain or numerical budget.

For every initial state s and assignment a:
  All a (completed s).atoms iff All a s.atoms.
For every derived fact f, both generated equality atoms occur in completed s.
For every s, the number of generated batches is at most 4*n. The finite Horn
engine has no unprocessed enabled scalar fact after its computed capacity.
For every public registry/slots/Sources/Goal/state, successful replay iff s has
a model and the existing registry checker succeeds. On success, snapshots are
at most 1+4*n and the existing source-derived rebuild/visit bounds apply.

## Deliberate boundary

This is not a general state-changing role scheduler: scalar rule edges are read
from the initial ordinary state; generated batches only expose already-derived
scalar equalities. New variable edges, new slots, real-source declaration batch
generation, invocation identity, associated rule generation and final four-way
classification remain open. All five B4 bridges remain incomplete. No language
rejection is inferred from this implementation-fragment restriction.
