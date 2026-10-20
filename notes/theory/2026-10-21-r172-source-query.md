# R172 source-keyed observation surface

Status: **provisional borrowed query; not independently reviewed; no probe run**.
The query changes observation only. It adds no source admission, solver retention,
propagation, inference behavior, or public product API.

`CandidateInference::source_provider_observation` selects store provenance by the
leased HIR occurrence/local-slot keys before applying its bounded presentation
limit. It retains the complete Cause, FactId and SemanticFact references. It then
returns every occurrence-matching Origin candidate and walks retained context
dependencies forward from each candidate relation. Derived, FunctionPort,
Transport and ordered Replay data are represented by typed fields; both Replay
input keys are retained even when only one is on a path from the selected seed.
The route selection uses the exact forwarding Apply's checking occurrence, its
resolved module callee source occurrence, module target and NativeInterface
callee/demand Terms. Capture graph, matching bounds, snapshots and FreshUse maps
are emitted only for that selected route.

The source-to-consumer discriminator is deliberately unavailable. The queried
Origin key does not distinguish the direct source drain from a Replay child that
reuses the same occurrence/cause, and the retained records do not authenticate a
consumer FunctionPort relation. Capture and FreshUse maps currently retain their
owner records through the existing borrowed observation row, whose payload is
opaque Debug data. Accordingly the result reports
`direct_source_drain_attribution=Unknown`, `captures_structured=false`,
`maps_structured=false`, and `consumer_relation_join_complete=false`.
`source_to_consumer_discriminating()` therefore returns false. These fields do
not certify the candidate construction in the R172 proof revision 1 history.

The leased harness uses the unchanged R171 source fixture and its source ranges
to locate terminal Lambda, body Name, relay's forwarding Apply and argument Name before
passing the branded occurrences and the proof's source-local slots to the query.
It is a diagnostic artifact only. It was not built or run. The conditional Y3
probe is **NOT_RUN** because the reviewed construction correction leaves direct
source-drain attribution unknown and this query cannot discriminate the required
same-provider source/Capture/map/consumer join.

The proof worker's revision 2 governs: source facts and candidate Origins may be
enumerated, but no direct-drain ancestry, concrete provider tuple, parent theorem,
or production gate is closed. R169, R70/R71/R165/R166/Replay, original A/B,
F1/FK1 and production remain OPEN.
