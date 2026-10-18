# Sprint — observe and reconstruct Replay constructor lineage

Status: authorized successor after the CLEAN closeout of
`npair-replay-cross-route-ownership-20261018`. The original parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains **OPEN**, with
original quantifiers, source domain, accepted semantics and fixed `c` intact.
No semantic adoption follows from this sprint. Astra budget is **0**.

## Fixed outcome

Use construction-time, test-only observations plus one exact source test to
classify the observed cross-route Replay join, or name the first still-missing
constructor fact. Keep Module route0/use1 and route1/use2 distinct. The report
must connect capture row identity and classification, reconstruction map,
lower relation producer/admission/emission, ordered Function ports, Replay
child ancestry and actual drain result.

The previous CLEAN audit established that the existing census omits row keys,
representatives, capture/reconstruction levels and flags, graph boundaries,
route row maps, source-occurrence attribution and concrete Replay port pairs.
Its output remains the pinned observation gap; do not rerun the old diagnostic.

Allowed outcomes:

1. source-grounded legitimate borrowed/shared cross-route join;
2. demonstrated loss of a required fresh separation/map, with the exact
   constructor and minimal repair prerequisite; or
3. a precise named fact that the new observation still cannot expose.

Do not change an authentication predicate, assertion, error path, accepted
semantics or production behavior. A passing observation test is not a proof of
the parent theorem. Preserve every existing assertion and mutation control.

## Frozen inputs

- Prior CLEAN audit note:
  `notes/theory/2026-10-18-replay-cross-route-ownership.md`
  SHA-256 `572884a8df2e8adc19eb1a8121277c77784e3c02fa9925729e292dd629f40308`.
- Prior audit handoff:
  `tasks/agent-loop/inbox/20261018-replay-cross-route-ownership.md`
  SHA-256 `f2c93d65ba96e4a256010e2942096ca21ef714b5b06d81573701eb0b960948ed`.
- Previous code inputs: `candidate_scheme.rs`
  `0c55d3d47bc88166a68eb5f5797043b136a2d2bc0ace55de832e8e27ca20a07f`;
  `candidate_context.rs`
  `f2ecbadcc33e4439c57429cb6a6ce5bcdfd5c3131f5b5ebb9d1e03a0e224f569`;
  `shadow_apply.rs`
  `6508a3f39a6d3742110ca1f33e927fa26bd3b112c3f378fc345294675b7f69e3`;
  `candidate_source.rs`
  `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`;
  `candidate_call.rs`
  `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`.
- Prior diagnostic stdout
  `tasks/agent-loop/runtime/20261018-replay-positive-provenance.diagnostic.stdout.log`
  SHA-256 `05c536a2d2a5265687b16362fec6d0909a8dfbed178d69c8feb90a83972cf813`;
  stderr SHA-256
  `6966e24792eb97eaf26498f7e975cdc919fd0d19cb283666b613d78adcac49a3`;
  metadata SHA-256
  `6e0dda42a13b1ff8273904a0a4e239ea7d77b789d9cc94ec7d55bfa5ed740f47`.
- Current selector decision: backward provenance slice plus per-route
  reconstruction commuting square. Source support alone is not occurrence
  attribution. The old failing diagnostic is not authorized for rerun.

At intake, verify every frozen input hash. If any changed, stop and return the
exact mismatch for Luna adjudication; do not silently rebase.

## Leases and outputs

Implementation author (`implementer`, Luna/high), exact writable paths:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `tasks/agent-loop/inbox/20261018-replay-constructor-lineage-impl.md`

Proof author (`prover`, Sol/high), exact writable paths:

- `notes/theory/2026-10-18-replay-constructor-lineage.md`
- `tasks/agent-loop/inbox/20261018-replay-constructor-lineage-proof.md`

Luna integration/runtime paths:

- `tasks/agent-loop/current.json`
- `tasks/agent-loop/runtime/20261018-replay-constructor-lineage.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-lineage.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-lineage.meta.json`

All other paths are read-only. No scratch files, dependencies, descendants,
semantic rules, compiler call-site policy or broad fixtures may be edited.

## Required observation and proof

Instrumentation is test-only and must retain, for each of the two uses:

- capture occurrence/key, canonical representative, captured level and
  `non_generic`, graph boundary and stored `local` decision;
- reconstruction source/canonical representative, current level and
  `non_generic`, per-use row-map entry and actual reconstructed row image;
- route owner and use identity, without collapsing sibling uses;
- lower Relation58 source occurrence and constructor ancestry, admission56
  cause, emission56 record and physical endpoint;
- lower and upper Function roots and four ordered FunctionPort dependencies
  each, linked to exact child relations;
- retained Replay dependency, child identity, and actual drain/return result.

The proof note must derive both capture/reconstruction branches from their
source guards, then apply the reviewed runtime observation to a complete
producer-to-consumer path. Mark each statement as source fact, observation,
conditional inference or still unknown. State whether any compiler correction
is justified, and state the exact repair prerequisite. Do not claim that this
single specimen proves receive transport universally or discharges original
`?e_Op`, F1/FK1, Call, soundness, principality or termination.

Fresh review must check source/hash integrity, test-only containment, unchanged
authentication and mutation controls, exact route/use identity, every reported
constructor edge, all ordered ports and consumer/drain ancestry. It must
falsify a wrong freshening branch, representative change, unsupported source
edge, owner collapse, port mismatch, or drain mismatch.

## Execution gate and resource envelope

Total new envelope: **1560s**, allocated once:

- implementer source work: 600s;
- prover derivation and artifact: 420s;
- fresh instrumentation/code review before execution: 120s;
- one exact test/runtime attempt after CLEAN instrumentation review: 120s;
- final independent source/proof/runtime review: 180s;
- Luna integration and record updates: 120s.

Astra 0, no descendants, at most one Cargo process. First freeze source edits
and obtain the instrumentation review. Only on CLEAN may Luna run exactly one
new test selected by its full test path with `--exact --nocapture`; capture
stdout, stderr, command and exit status to the three leased runtime paths. No
old diagnostic rerun, retries, broad suite, formatter, or build-only command.
After the run, freeze the proof artifact and send the final packet to an
independent reviewer who authored neither lane. A failing observation may
still be a useful diagnostic, but cannot be reported as a passing test.

Use the granted seconds conservatively; record author/reviewer STOP before
lease transfer. Unknown model telemetry remains UNKNOWN. This sprint closes
only with a reviewed classification or a precise named missing fact, honest
runtime receipt, and original parent closure still stated as **0** unless a
separate original theorem obligation is fully proved.
