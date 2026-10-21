# Sprint R199 — Relay Capture bound-origin trace

Status: CLOSED, source-surface obstruction after one failed query launch.
Branch / baseline: `research/simple-sub-intrusion` / `cbd0de10e24f1e0dbac0b9229a1983af4b707d39`.
Authority: unchanged computation-forwarding preservation parent §§1, 6–7 and R183-FRONTIER-COVERAGE-1. No theorem narrowing or production authorization.

## Outcome

Trace the relay Capture's local negative-side owner bounds (relations 53, 56,
57, 62) back through retained admissions/emissions, source occurrence origins,
and Replay/transport dependencies. Determine whether any one local owner has
the two distinct source bounds needed by the R183 frontier witness, and
whether the shared Effect 9 owner has a source-authenticated edge to that same
local row. Apply the exact result to the universal frontier premise.

Success evidence: a relation/BoundKey/admission/emission/source-occurrence
table with complete query coverage, or a field-level obstruction naming the
first missing link. Capture's complete row list rules out an unobserved second
edge on a local owner at that readback point; shared-owner physical bounds may
remain outside Capture and must be queried separately or marked missing.
Structural IDs and endpoint equality alone do not count. Parent/A/B/source-
native/production gates remain OPEN unless an original-source path closes.

## Exact boundary

Read R183 and R187–R198 receipts and exact current source owners in
`candidate_context.rs`, `candidate_effect.rs`, `candidate_scheme.rs`,
`candidate_source.rs`, `shadow_apply.rs`, local source observation, and `lib.rs`;
record hashes before relying on source. One bounded offline Cargo query may use
only `target/r199-bound-origin/`, must be removed at closeout, and must not be
retried after invocation failure. No source edits, tests, or new observer.

Exact durable writes: this contract, `tasks/agent-loop/current.json`, and
`notes/theory/2026-10-21-r199-relay-capture-bound-origin.md`. No other dirty
file may be edited or staged. No subagents or independent review under the
user's explicit solo-work rule. Budget 600 seconds, one Cargo process maximum,
no carryover. Preserve original quantifiers and all production gates.
