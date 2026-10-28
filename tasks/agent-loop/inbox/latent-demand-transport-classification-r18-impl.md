# R18 implementation handoff

Status: **FROZEN / STOPPED**

## Assignment and artifacts

- Sprint: `LATENT-DEMAND-TRANSPORT-CLASSIFICATION/r18`
- Contract SHA-256: `fedd227744b66af19d5544315130233c4fb666667c996fcafa92dbb8ebf99e9a`
- Manifest SHA-256: `d07167958cdb5f93a5370d48568a7a0ab4afc8b8ec31a02ffbdb359848a5b455`
- Sole changed source path: `isolated/latent-demand-transport-classification-r18/crates/yu-solver/src/candidate_scheme.rs`
- Frozen candidate SHA-256: `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`
- Handoff path: `tasks/agent-loop/inbox/latent-demand-transport-classification-r18-impl.md`

## Behavior added

Within the existing `replay_rows` loop, each row now emits a start record identifying call, FreshUse identity, child/lower/upper relation IDs and root. The existing pre-call skips emit explicit `NO_NATIVE_CALL` or `NO_COPIED_PORTS` outcomes and an end record with zero callbacks and no returned evidence. For rows reaching authentication, the existing observer closure increments a local callback counter and emits the same `(owner, route, stage)` classification record with that row identity. Each row then emits an end record with callback count and `evidence.is_some()`.

The returned `Option<DemandTransportEvidence>` remains the one value passed to the existing `emission_cases` insertion unchanged. Authentication inputs, callback invocation order, route traversal, guards, fixture, assertions and semantic behavior are unchanged. The diff from the pinned R17 partial candidate is confined to this loop at lines 8417–8476: 44 added lines and 3 replaced lines.

## Correspondence and limits

The instrumented row links its replay call/use and child/lower/upper relation IDs/root to the existing candidate native call and `authenticate_demand_transport_observed` invocation over retained FreshUse route maps. It records what that invocation returns and which observer events it emits; it does not establish a source-level Call/use theorem, demand capture/import law, constructor-to-consumer correspondence, adequacy, or source/native semantic correspondence. The source lane must map frozen run output to those source occurrences. No test has run in this lane, so row counts, callback sequences, skips and returned evidence remain unknown.

The output records only callbacks actually emitted. A rejection callback can return from the whole authentication call, while `original-root-absent` can continue traversal; downstream interpretation must not assume every route was visited. A zero-callback `None` only supports that no route emitted a matching-use event, absent source mapping.

## Evidence, checks and boundaries

Reused the R17 revision-1 observer candidate as pinned by the R18 manifest (`f0f8c15a78620ff34c85433fefbf842f4b716831207057a1804e7a27f2f77a3d`); R17 was closed incomplete without Cargo, so it is not validation evidence. Compared the frozen R18 candidate to the R17 candidate with a read-only unified diff and confirmed the sole hunk is this loop. Verified the contract and manifest hashes above and computed the frozen candidate hash above. No Cargo, test, build, formatter, checker, or Git command was run, as required.

This is provisional, test-only diagnostic instrumentation. Falsifier: a frozen execution whose row start/end identities do not pair one-for-one with `replay_rows`, or whose callback count differs from emitted classification events, invalidates the row-level report. Luna owns deciding retention/removal after the one-shot evidence is archived; this handoff does not authorize production cutover.

Unresolved: source parent `YulangClosure.SourceProblem.InferenceSoundness`, Call/shared-witness, Generalize allocation, source/native correspondence, effect hygiene, principality, termination and production gates remain OPEN. Preserve `EvidenceCoverage { gaps: 56 }` unless exact output changes it. No source theorem or native adequacy claim is closed here.

## Runtime and next step

- START acknowledged: `2026-10-28 13:04:18 UTC`.
- Requested assignment model/effort: Luna/high.
- Observed model/effort: not independently exposed in this worker runtime; no substitution was made.
- Grant: original 300 seconds, no reset; this lane used under 300 seconds and stops here.
- Next related in-envelope step: fresh independent pre-run review of this frozen candidate; after ACCEPT, Luna may perform the single contracted Cargo attempt. This worker does not resume without a new explicit assignment.
