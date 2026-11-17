# Finite actual raw View typed support

Enumerate ordinary atom reads and, over all finite slots, slot type reads,
optional head-equation reads and every nominal descriptor type-parameter
endpoint read. Intervals use already enumerated slot types. Row parameters and
row expressions need no typed names because all rows are preserved globally.
Prove exact model invariance from equality on this explicit support, with no
abstract Stable assumption. Apply it to compiled old views and fresh solve
whose targets avoid that support; compose with ordered old-block recovery.
This covers all fields used by actual RawView243.View.Models, but not live
sites, packet/history/cache enumeration, operational steps or termination.

Verified: GeneralNominalViewSupport249 and GeneralNominalOrderedRawExpansion249
both pass focused Lean --trust=0 -DwarningAsError=true in cycle247-clean.
The latter supplies view_preserved, raw_forward and raw_public_models_iff.
The existential equivalence shares one assignment across actual raw state,
ordinary consumer constraints, old/fresh block and public coordinates. It
requires explicit fresh-target separation from the compiled view's calculated
support and rewritten consumer reads; it does not assume abstract stability.
As with ordinary expansion, forward recovery does not need old SafeOrder;
backward block construction does. No old Lean file was changed.

## Verified complete compiled packet support

Seven further modules pass strict --trust=0 -DwarningAsError=true:
LiveSupport249, OriginSupport249, ProjectionSupport249, SchemaSupport249,
EffectSupport249, PacketSupport249 and OrderedPacketExpansion249 (all prefixed
GeneralNominal). Live support includes output targets even though Site.Holds
only constrains arguments. Origin exact typed evaluation gives literal
same-witness observation transport, including source leaves. Projection covers
anchors/tests/captures and both cross-capture conditions. Schema covers actual
requirements/uses/tests; Effect covers all recursive expression constructors
and lists with literal evaluation equality.

PacketSupport249 enumerates all eight actual Packet.Holds components. The
expanded-target theorem uses fresh-target separation from this computed list,
not an abstract Stable law. Its public_models_iff combines an arbitrary finite
Plan list with arbitrary consumer atoms, block equations and public coordinates
at one common assignment on each side. Protected packet/raw/consumer support
and public coordinates still require source-side production. Finite lists
here are supplied inputs, not a verified enumeration of operational
current/history/cache storage. No acceptance, progress or Acc claim follows.
