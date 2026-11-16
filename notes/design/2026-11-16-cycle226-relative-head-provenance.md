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
