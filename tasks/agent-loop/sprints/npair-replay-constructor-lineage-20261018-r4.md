# Sprint — isolate rejected Replay observations in a new test

This revision adopts the hash-verified r2 rejected source bytes as the explicit
current test-instrumentation baseline. It does **not** establish r2's
byte-level provenance, validate any prior production refactor, or authorize
production changes. Original theorem `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR-20261017` remains **OPEN**, closure **0**, with fixed `c`,
original quantifiers, source domain and accepted semantics unchanged. Astra 0.

## Fixed outcome

Add one separate `#[test]` to the existing test module. It must pass while
observing the already-known authentication rejection and emitting all
classification evidence before any assertion that depends on authentication.
Report actual drain completion only when tied to matched child receipts;
otherwise distinguish `NotReached` with source control-flow evidence from
`NotRetained`, which leaves reachability unknown.

The new test's exact full path is:

`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`

No old exact test rerun, no retry, no broad suite and no source changes outside
the new test addition. `candidate_context.rs` is read-only. Do not alter
authentication predicates, wrappers, assertions, error paths, or mutation
controls. No runtime/build/test until fresh independent instrumentation review
returns CLEAN.

## Frozen inputs and explicit baseline

- Prior CLEAN cross-route audit note
  `notes/theory/2026-10-18-replay-cross-route-ownership.md`, SHA-256
  `572884a8df2e8adc19eb1a8121277c77784e3c02fa9925729e292dd629f40308`; handoff
  `tasks/agent-loop/inbox/20261018-replay-cross-route-ownership.md`, SHA-256
  `f2c93d65ba96e4a256010e2942096ca21ef714b5b06d81573701eb0b960948ed`.
- r3 provenance-recovery result: exact pre-r2 inputs were not recoverable;
  current r2 rejected bytes were copied and verified. The r3 author's final
  record is preserved in current state. No claim of original-input recovery.
- **Explicit current baseline:**
  `tasks/agent-loop/runtime/20261018-constructor-recovery.candidate_scheme.rejected.rs`
  SHA-256 `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`;
  `tasks/agent-loop/runtime/20261018-constructor-recovery.candidate_context.rejected.rs`
  SHA-256 `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.
- The older original-source reference hashes remain documented in r2/r3 but
  are not this sprint's reconstruction targets.
- Pinned old diagnostic remains reference-only. Its runtime has already shown
  that the old test fails at authentication; this sprint never selects it.

At intake, verify every pin and require the live sources to equal the explicit
baseline snapshots before editing. If they do not, stop and report the exact
mismatch. Do not overwrite the snapshots.

## Exact paths and leases

Implementation author (`implementer`, Luna/high), exact writable paths:

- `crates/yu-solver/src/candidate_scheme.rs` — add only the new test function.
- `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-impl.md`.

`crates/yu-solver/src/candidate_context.rs` and both baseline snapshots are
read-only. No scratch paths, production changes, fixture changes, dependencies
or descendants.

Proof author (`prover`, Sol/high), exact writable paths:

- `notes/theory/2026-10-18-replay-constructor-separate-test.md`.
- `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-proof.md`.

Luna integration/runtime paths:

- `tasks/agent-loop/current.json`.
- `tasks/agent-loop/runtime/20261018-replay-constructor-separate-test.stdout.log`.
- `tasks/agent-loop/runtime/20261018-replay-constructor-separate-test.stderr.log`.
- `tasks/agent-loop/runtime/20261018-replay-constructor-separate-test.meta.json`.

All other paths are read-only. Only the exact current source lease is renewed;
all r1/r2/r3 contracts and prior artifacts remain frozen.

## Required test and proof content

The new test must build the same source specimen, run ordinary inference, and
then independently observe (without requiring successful authentication):

- Module route0/use1 and route1/use2 as distinct identities;
- each route's capture key, representative, level, `non_generic`, boundary,
  stored `local` flag, reconstruction representative/metadata, canonical map
  hit/miss, first insertion order, and complete row image;
- the lower producer occurrence ancestry, Relation58 pair, admission and
  physical emission/readback;
- lower and upper Function roots, all four ordered FunctionPort relation IDs,
  endpoint pairs and source ancestry;
- actual Replay child identities and drain/return state, or a typed
  `NotReached`/`NotRetained` value with the exact derivation for that status.

The test must assert that the fixture is the pinned rejected specimen and that
the authentication result is `None`, then pass. A failed or absent observation
must fail the new test explicitly. All records required to explain the
rejection must be emitted before assertions that could panic. Never call
`expect` on successful authentication in this new test.

The proof note must reuse capture/reconstruction branch facts only as
source-conditional derivations, distinguish map miss from later hit, and bind
each observed edge to a source constructor. Separate source facts, runtime
observations, inference and unknowns. State whether the join is shared, a lost
fresh separation, or remains undecided. Authentication failure itself proves
neither ownership alternative. Do not claim universal receive transport,
original `?e_Op`, F1/FK1, Call, soundness, principality or termination.

## Independent review and execution gate

First, a fresh reviewer checks baseline hashes, that deleting only the new test
addition recovers the baseline scheme bytes, no context bytes changed,
test-only containment, preservation of the old assertion/mutation controls,
independent pre-auth observations, exact test identity and complete consumer
classification. It must check source-grounded drain status and every port/map
edge. Only **CLEAN** permits one exact invocation of the new test using
`--exact --nocapture`.

Luna executes that new test exactly once, captures command, executable/source
hashes, stdout, stderr and exit status, and writes only the three leased
runtime outputs. No old test, retries or broad suites.

Afterward, freeze the proof note and both handoffs. A different fresh reviewer
checks frozen source, runtime and proof. Reviewers author neither lane.

## Resource envelope

Fresh envelope **1080s**, no rollover from r2/r3:

- implementation 360s;
- proof 180s;
- instrumentation review 120s;
- one exact test/runtime 120s;
- final review 180s;
- Luna integration 120s.

Astra 0, descendants 0, one Cargo process maximum. Record stopped authors and
reviewers before transferring leases. Unknown model telemetry remains UNKNOWN.
No original parent condition closes unless independently fully proved.
