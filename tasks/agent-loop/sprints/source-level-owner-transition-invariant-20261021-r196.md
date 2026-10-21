# Sprint R196 — Source-level transitions and Capture ownership

Status: CLOSED, source-transition obstruction; parent open.
Branch / baseline: `research/simple-sub-intrusion` / `92bace9717ebe5ec1b1c56866fac1461ab2f7121`.
Authority: unchanged computation-forwarding preservation parent §§1, 6–7 and R183-FRONTIER-COVERAGE-1. No theorem narrowing or production authorization.

## Outcome and success evidence

Resolve the universal source-history step isolated by R183/R195: can an
accepted source transition make a bound owner shared (`level <= boundary` or
`non_generic`) while a required neighbor remains local, leaving the provider
Capture unable to follow the original constraint chain? Prove the needed
transition invariant across source-level initialization, typed extrusion,
candidate bound insertion, canonical row merges, and valid rollback; or produce
the first actual source constructor sequence that falsifies it and apply that
sequence to the three-edge frontier witness.

Success requires a constructor-by-constructor induction with exact read/write
owners and order, including the merge level-minimum/non-generic-OR transition
and both physical bound sides, or a fully joined accepted-source witness with
original source admissions, canonical owners, Capture decision and all three
edges. A synthetic state, unit-only test, candidate row match, or green test is
not source evidence. If neither result closes, state the precise first missing
constructor premise and its owner; the unchanged parent remains OPEN.

## Inputs, leases and limits

Read the R183/R195 audits and the exact transition owners in
`candidate_source.rs`, `lib.rs`, `candidate_extrusion.rs`,
`candidate_intrusion.rs`, `candidate_context.rs`, `candidate_effect.rs`, and
`candidate_scheme.rs`. Verify and record byte hashes before relying on them.
No source edits, tests, Cargo probes, or observer changes in this sprint.

Exact durable writes: this contract, `tasks/agent-loop/current.json`, and
`notes/theory/2026-10-21-r196-source-level-owner-invariant.md`. No other dirty
file may be edited or staged. No subagents or independent review under the
user's explicit solo-work rule. Budget 600 seconds, no carryover. Preserve the
original parent/A/B quantifiers, source/native correspondence, and production
gates as OPEN.

## Method and falsifier

Use a transition-induction ledger over every production writer of component
levels, non-generic bits, forest representatives and physical bound ownership.
The candidate invariant must say when an extant original edge can cross from a
shared endpoint to a local endpoint after each transition and whether its
physical origin is transported to the canonical key. Falsify the proposed
invariant with an accepted Name/Lambda/Apply/merge history that leaves the
shared owner unexpanded and both required local-owner edges uncompensated.
Otherwise identify the exact induction case whose source admission or
rollback premise remains unproved. Apply the result directly to
R183-FRONTIER-COVERAGE-1.

## Outcome and closeout

The production writers are bounded to source-level initialization, extrusion
lowering, and merge minimum/OR, with valid rollback restoring the prior row
state. Existing adjacency is closed under typed extrusion. The remaining
induction case is a one-sided signed copy whose bound fiber is transferred by a
canonical merge to a lower-level representative without lowering every
neighbor. This is a real transition-level obstruction, but no accepted
source-generated sequence realizing all three frontier edges was established.
The original universal premise remains OPEN. Full hashes and reasoning are in
`notes/theory/2026-10-21-r196-source-level-owner-invariant.md`.

No code edits, tests, or Cargo runs occurred. R196 used 180s of its 600s
allocation; remaining time expired without carryover. Solo primary; no
independent review. Parent/A/B/source-native/production gates remain OPEN.
