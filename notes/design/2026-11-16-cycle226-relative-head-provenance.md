# Cycle226: relative head source provenance

The relative packet of225 no longer repeats old raw constraints. Its ordinary
atoms still need a precise ownership theorem before attempting trace Overlap.
For every packet, bound their sources by the old base slots plus only this
packet declaration's local aggregate targets. Cross and self-check atoms read
base slots; merge atoms additionally read this declaration's allocated p0/p1.
Do not replace base slots by all raw sources, which would reintroduce the
constraints removed from the relative support list.

Combine that bound with224's exact report origins to classify relative head
sources. An allocated origin absent from the base/report-origin support must
be a p0/p1 input target of this packet's own invocation and declaration.
This is a single-head provenance result, not full trace freshness. Effect and
schema sources, protected Overlap, common-model existence, and EvidenceNode
remain open. No change to semantics, candidate selection, or old theorems.

Further source review found that224 protects every base slot even though
ProjectionModels reads only anchor and capture bounds. A second module gives
an exact frame with these bounds and actual report origins; no unrelated base
slot is protected. Cross/merge inputs and self-check sources likewise need
only capture/checked bounds. This addresses the next overapproximation rather
than assuming arbitrary refreshed slots are historically fresh.

## Reachable packet route

The generic projection frame above is useful but still overapproximates a
reachable packet. CountedRawHead216 already proves, for a reachable Frame and
a journal model with actual Agreement, that HeadModels is exactly its merge
atoms. Packet headSchema entails Agreement (HeadSharing220). Therefore transport
the non-head packet components first, recover Agreement on both assignments,
and transport just merge atoms. This removes cross/self-check/projection reads
from the reachable relative packet delta without dropping their semantics.
The source, point-root, ground-root, coverage, reachable-path and Frame hypotheses
are explicit. This still does not prove aggregate Overlap; it removes another
unnecessary source-protection obligation on the route to that proof.

The reachable `packet_iff` and `install_depends` are verified. The latter takes
actual Installable, not an assumed packet satisfiability or Overlap conclusion.
Its frame comes from that Installable. No new Agreement premise is needed:
Rest includes headSchema, and transport of Rest supplies Agreement on both sides.

Remaining proof obligations are now more sharply separated:
1. Merge inputs/targets: provenance of currently observed endpoint bounds and
   whether a protected p0/p1 aggregate already has its required extrema.
2. Non-head schema/effect sources: extend the existing purpose8 readback to
   relevant p0/p1 occurrences, or derive redundancy from old journal Models.
3. Close Overlap for every selected current Frame, using historical replay for
   already-installed same-key aggregates. No general theorem here supplies it.
The arbitrary Refresh support certificate still allows old reserved names in
its raw snapshot. Neither base slots nor the exact read bounds are automatically
historically fresh. Thus the one-head ownership theorem must not be promoted
to a full-trace absence theorem without another argument.
