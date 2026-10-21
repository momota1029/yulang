# R198 — Merge parent source-origin join

Status: source-qualified candidate relation/transport join; parent theorem open.

Source hashes at the query:

| File | SHA-256 |
| --- | --- |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_source.rs` | `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a` |
| `candidate_context.rs` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_effect.rs` | `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1` |
| `candidate_scheme.rs` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |
| `shadow_apply.rs` | `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4` |
| `local_source_observation.rs` | `dd2ec5b5b0efb55966e39b54cfcba19b8fc8a6edc33247cf4436f247d403cb38` |
| `lib.rs` | `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436` |

## Exact occurrence and source receipt

The R187 `bridge`/`relay` fixture was rerun through
`source_provider_observation` for source Apply occurrence 9, slot 0
(`bridge` calling module `outer`). The result was complete for facts, origins,
and dependencies. It returned one direct source origin:

```text
graph 0; occurrence 9 / slot 0; relation 21;
cause occurrence 9 / slot 0; incoming_relation=None; replay_ack=None;
created_seed=21; selected_relation=21
```

The same retained dependency list relates source relation 21 to Replay child
22 with parents 18 and 21. This distinguishes the direct source seed from its
later Replay descendants. The query's provider-route and consumer-relation
joins are false, however: source-origin/dependency completeness does not
provide an end-to-end provider Capture/consumer receipt.

## Join to the intrusion event and transported keys

The intrusion observation maps event 0 to the same source checking occurrence
9 / slot 0, with origin local definition ordinal 0 (`bridge`) and receiver
module definition `outer`. All four settled intrusion parent links carry
`source_events=[0]`. The source relation 21 dependency view contains these
exact transport witnesses:

| Dependency ordinal | Witness source key → destination key | Reason | Corresponding settled parent |
| ---: | --- | --- | --- |
| 39 | Value 26, positive, IntPositive → Value 24, positive, IntPositive | `ParentCopy { parent_index: 0 }` | Value 26 → Value 24 |
| 51 | Effect 9, negative, Effect 26 → Effect 9, negative, Effect 9 | `EqualityCanonicalization` | Effect 26 → Effect 9 |
| 53 | Effect 25, positive, Effect 27 → Effect 25, positive, Effect 25 | `EqualityCanonicalization` | Effect 27 → Effect 25 |
| 55 | Value 9, positive, Value 27 → Value 9, positive, Value 9 | `EqualityCanonicalization` | Value 27 → Value 9 |

The ParentCopy witness includes the exact parent index. The other three
transport witnesses match the final copy and representative identities in the
parent table; their `EqualityCanonicalization` reason does not itself carry a
parent index. Together with the common exact source event and source relation,
this is stronger than matching numeric endpoints alone: relation 21's retained
dependency path records the source-key transport, and event 0 records the
source-associated settled parents.

## Remaining gap

This join authenticates some source relation to rehomed keys in this candidate
run. It does not make the R183 three-edge witness. In particular, the relay
Capture includes local owner `Effect(29)` with bound to shared `Effect(9)`
(relation 53), but no readback joins a second distinct bound on that same local
owner, or a shared-owner edge from Effect 9 to that same local Effect 29.
The owner row 9 is intentionally not expanded by Capture. The source query
also reports no complete provider/consumer route join. Capture coverage mask
120 for relation 53 still omits antecedent, processing/ordinary-seed and
Replay-use lineage.

Thus R198 closes the source-origin-to-some-merge-transport link for occurrence
9 and identifies the remaining discriminant: authenticate both required
local-owner admissions and the shared owner's edge to the same local owner (or
an independent reached path that supplies it). No source-qualified
counterexample or universal source-history invariant has been established.
Original parent/A/B/source-native/production gates remain OPEN.

Probe driver SHA-256:
`ee4126abafe3d517e89627fd3ab05255e1224e2ef6de022727c521da76ca7766`.
Probe output SHA-256:
`59661646f25d9ed3c305a755c59fa59ca5a93a0d3fd03ecca310027ab9777ff7`.
One offline Cargo invocation succeeded. Scratch was removed from
`target/r198-source-origin/`. No source edits or tests occurred. Solo primary;
no independent review.
