# R201 — Event-set to bound and Capture join

Status: source-level relation/fiber join established; original source-bound/provider correspondence remains OPEN. No theorem or production gate is closed.

## Pinned sources

| Owner | SHA-256 |
| --- | --- |
| `candidate_context.rs` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_effect.rs` | `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1` |
| `candidate_extrusion.rs` | `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332` |
| `candidate_scheme.rs` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |
| `candidate_source.rs` | `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a` |
| `shadow_apply.rs` | `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4` |
| `local_source_observation.rs` | `dd2ec5b5b0efb55966e39b54cfcba19b8fc8a6edc33247cf4436f247d403cb38` |

The audit used the frozen R194–R200 receipts. It ran no Cargo process or tests and made no source edits.

## Constructor path for a relation-bearing physical bound

For an ordinary owner emission, `candidate_bound_origin_with_evidence` chooses the processing pair (or its explicit fallback), asks `candidate_context_bound` for a relation, and retains that relation on the `BoundAdmission`. `candidate_context_bound_for` constructs a child relation for the bound key, copies the current processing relation's source-set identity into the child, records `Dependency::Derived { child, parent }`, and attaches that child to the exact `(BoundKey, relation)` fiber. The admission also retains `OwnerEmission { processing }`.

The evidence admission does not turn that processing pointer into a complete antecedent chain. For `OwnerEmission`, its coverage explicitly records `ProcessingAntecedentsUnavailable`, `OrdinarySeedAuthenticationUnavailable`, and `MissingAntecedent`. The child relation can carry source event-set identity, but the admission does not state which original Name/Lambda bound or source seed licensed this exact physical edge.

`candidate_insert_bound_with_evidence` selects the concrete owner lane, records an admission, appends the bound, reads the exact physical slot back, and rejects a mismatch. When capture is requested, it registers that bound. Only after successful readback does it emit a `BoundEmission` carrying the exact `BoundAdmissionId`, physical slot, bound key and constructor-after-append phase. Thus a retained admission and its emitted vector entry are separate, explicitly joinable records.

`Capture::bound` enumerates each physical key with each attached relation. `evidence_snapshot(BoundKey, relation)` selects that exact evidence group and captures its admission/emission heads plus coverage. Missing relation, group, admission or emission becomes an explicit coverage gap. The snapshot therefore joins one captured physical bound fiber to its retained evidence group; it does not manufacture missing source antecedents.

## Where the current observation stops

R195's relay Apply 18 rows still say: `Effect(23)` relation 56 reaches `Effect(12)`; `Effect(12)` relations 57 and 62 reach `Effect(23)` and `Effect(29)`; `Effect(29)` relation 53 reaches shared `Effect(9)`. No single local negative owner in that Capture has the R183 pair of one edge to a shared row and a distinct second edge.

The local-source observation returns the exact Capture graph, bound rows, evidence snapshots, maps and Replay dependencies. It does not return the relation's source-event set, corresponding `BoundAdmission` records, or the `BoundEmission` chain. The ordinary-provider observation does return admission/emission records, but only for relations selected as retained AE/RE FunctionPort parents; it is not a query over arbitrary local Capture relations 53/56/57/62. So the source-level data model has an identifiable join key, while the current run-level read API does not expose the fields needed to instantiate the join for this fixture.

Even a direct internal read of each relation's source-event set would authenticate only Apply-level event lineage. The `OwnerEmission` coverage gaps still leave the original source-bound admission/seed to physical edge path unproved. The shared Effect(9) row is nonlocal and is not expanded by this Capture; its physical bounds and a qualifying edge back to the same local owner remain uninspected.

## Parent application and next evidence

This closes the R201 source-constructor question: relation/source identity, exact physical admission/emission, and Capture snapshot are structurally joined by retained relation and evidence IDs. It does not close the universal source-to-provider premise. The concrete R195 frontier still lacks the three-edge witness inside its enumerated local rows; R198/R200 event and transport results do not supply the missing OwnerEmission antecedent.

The next useful artifact is a bounded post-solve read of existing relation source sets, evidence groups, emissions and Capture snapshots, with no new persistent solver state. It should answer whether the R187 Apply 18 event set actually reaches each of the four Capture fibers and show the exact OwnerEmission coverage gaps. A candidate fixture remains a fixture; the original all-routes proof must separately establish the same construction for every supported source history, including rollback, transport, replay, merge and shared anchors.

Original quantifiers, parent/A/B/source-native correspondence and production gates remain OPEN. R201 closed after 120 seconds of its 300-second cap, no carryover. Solo primary; no independent review.
