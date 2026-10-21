# R199 — Relay Capture bound-origin trace

Status: source-surface obstruction; no candidate-run query result. Original parent and every A/B, source/native and production gate remain OPEN.

## Scope and execution receipt

R199 was scoped to trace relay Capture relations 53, 56, 57 and 62 through bound admissions/emissions, source-occurrence origins, and Replay/transport dependencies. Current source pins at inspection:

| File | SHA-256 |
| --- | --- |
| `candidate_context.rs` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_effect.rs` | `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1` |
| `candidate_scheme.rs` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |
| `candidate_source.rs` | `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a` |
| `shadow_apply.rs` | `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4` |
| `local_source_observation.rs` | `dd2ec5b5b0efb55966e39b54cfcba19b8fc8a6edc33247cf4436f247d403cb38` |
| `lib.rs` | `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436` |
| R183 source-to-Capture receipt | `0fe3afdc4ddfd1d3b8979bf34497e395bef06836a199cb6735a39eb84c43a28d` |
| R195 concrete Capture receipt | `351ff6d37420ebce15a47412d5879a6b809f51e4d454859f689d6e88f234d951` |

One Cargo invocation was attempted with an isolated manifest and target directory under `target/r199-bound-origin/`. Cargo exited 101 before compilation because the nested package was considered part of the root workspace but was not a workspace member. The contract prohibited retry after invocation failure, so no second invocation was made. Driver SHA-256: `012dfe29c6043e88d59444ed6825e4ab32d83e3c5e34e0be741ceeac196f01e6`. Captured error output SHA-256: `c6a0eab55e3799e9e082413b91cd950346546dcd4652d1b2a74b6aeb1bb31093`. The leased scratch directory was removed. No solver result, source-query output, source edit or test run is claimed.

## What the current observation surface can join

`source_occurrence_observation` selects exact source facts and matching Origin candidates and reports list completeness. Its contract expressly leaves source-vs-Replay attribution and Capture reachability as separate joins. `local_source_provider_observation` joins one local Apply to its local route, retained Capture/map rows, and Replay dependencies touching the direct source relation. It reports that a Replay-child completion receipt is unavailable and leaves `preservation_complete` false.

The Capture rows preserve the graph, captured-bound and snapshot records. They are structural Capture inputs, not constructor-event history. The exact `BoundAdmission` record contains a bound, origin pair, optional relation, cause and coverage. `BoundEmission` separately contains the admission ID, physical slot and constructor-after-append readback. These are the records needed to distinguish an admitted edge from a physically emitted edge.

The existing `ordinary_provider_observation` does expose admissions and emissions, but only while iterating retained AE/RE `FunctionPort` dependencies and attaching rows to each FunctionPort's parent relation. It is not a general relation-keyed admission/emission census. Consequently, the public local-source observation does not currently provide a direct arbitrary-Capture-relation-to-admission-to-emission join for 53/56/57/62. Matching numeric relation IDs or endpoints cannot fill that missing link.

This identifies the first API-level obstruction, not a measured result for this candidate run. Since the only Cargo attempt failed before compilation, R199 did not establish which of those four relations have retained admission/emission rows or which source occurrence, if any, authenticates them.

## Application to the retained frontier

R195's prior candidate readback remains the concrete Capture evidence: in relay Apply 18, local negative owner `Effect(23)` has relation 56 to local `Effect(12)`; local `Effect(12)` has relations 57 and 62 to local `Effect(23)` and `Effect(29)`; local `Effect(29)` has relation 53 to shared `Effect(9)`. Thus no local owner in that enumerated Capture has both an edge to a shared row and a distinct second outgoing edge. R195 also records Capture snapshot coverage gaps, including mask 120 for relation 53, and does not enumerate shared `Effect(9)`'s physical bounds.

R198 joins source occurrence 9 / slot 0, relation 21, to several intrusion merge transport witnesses. That does not join relation 21 or its transported keys to the admissions and physical emissions for relay Capture relations 53/56/57/62. There is still no source-authenticated shared-`Effect(9)` edge back to the same local owner with a second qualifying edge.

The finite R183 frontier witness therefore remains absent from the previously enumerated local Capture rows, while the source/admission/emission path and shared-owner physical edge remain unjoined. This is neither a source-qualified counterexample nor a proof of the universal source-history premise. The original quantifiers and parent/A/B/source-native/production gates remain open.

## Closeout

R199 closed after one failed Cargo launch, charged 5 seconds of its 600-second cap, with no carryover. The next useful evidence needs a workspace-aware bounded query or an already-authorized direct read path that exposes the relation-to-admission-to-emission join; this receipt itself grants neither implementation nor observer-edit authority. Solo primary; no independent review.
