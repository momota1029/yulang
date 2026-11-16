# Cycle224: remove reservation overapproximation from projection support

The cycle223 installDelta theorem is sound, but its design note overstates the exclusion of reservation bookkeeping. packetSources includes GeneralNominalRawFrame179.reportSources, which includes GeneralNominalState.sources and therefore the full reserved list. Correct this explanatory claim without changing old proofs.

ProjectionModels reads finite base type slots, anchor/test origins, and capture origins. A new reportSources list retains exactly those classes of reads, and projection_iff proves its sufficiency. No change to ProjectionModels or language behavior. The current raw Models component is separate; its existing DefaultRawSupport213 theorem already omits reservation bookkeeping.

Next combine tight projection support with raw213 support for head_iff and total packet support. Still do not claim this removes every syntactically redundant ordinary source introduced by refresh, establishes historical ownership, or supplies Overlap. No Yulang2 behavior changed; no new execution claimed. All work remains local with cycle220/222 publication held.
