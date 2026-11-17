# Cycle231 supplement: finite version cover remains an operational obligation

I44's versioned aggregate allocation retains purpose0/1, the invocation,
declaration and binder name, and encodes the ordered captured endpoint list in
the positive position component. Purposes2–9 remain unchanged. Same captured
endpoints revisit the same aggregate IDs; an arbitrary step counter is not used.

## What the new allocation lemmas actually prove

GeneralNominalVersionedPool231.keyPool/sourcePool take an explicit finite
List Bindings. If a binding list is a member, all of its keys/reserved sources
are covered. Enlarging that list enlarges the cover. Equality of occurrences
for each visible declaration input name preserves keys/reservations. Equal
source seeds preserve sourcePool; propagate preserves that seed.

These are auxiliary finite-cover lemmas, NOT termination for the versioned
operational successor. The explicit finite candidate list has not been derived
for arbitrary reachable successor traces. reserved_covered leaves that premise
visible rather than hiding it behind a named wrapper.

## Exact old dependencies which cannot simply be reused

GeneralDictionaryDefaultEnumeration208.source_pool uses
GeneralDictionaryDefaultDepth208.reservations_finite and the old fixed
GeneralNominalAllocation.keys registry root. The old allocationPool enumerates
that fixed set across a bounded invocation genealogy. The old finite delta
cover then depends on the source pool and report enumeration.

Versioning makes purpose0/1 keys depend on the capture endpoints. Those endpoints
are read from the current snapshot, whose support can now include earlier
versioned aggregates. GeneralNominalReportEnumeration.one/many is finite for a
SUPPLIED finite source pool, but applying it with the new allocation pool as
both input and output would be circular without a new argument.

GeneralNominalReobservationSteps.Improves requires a strict increase in the set
of point nominal slots while preserving old pointness. It does not freeze all
existing point endpoint identities. Refresh certificates preserve support but
may expose additional slots from that support. These observations identify a
proof obligation, not a demonstrated infinite trace or a new counterexample.

## Required next bridge

Derive a finite content-version cover from the actual successor's initial
source, declaration/Paterson/K2 conditions, source-identity rules and observation
progress. Alternatively supply a justified well-founded measure that handles
new aggregate versions directly. Then transport the enumeration/termination
and the remaining boundary laws. Do not add an unproved finite-version
hypothesis to the advertised unconditional boundary theorem.

The old purpose8 actual centers stay unchanged (VersionedFrame231.binder_eq).
A different aggregate endpoint must not be mistaken for a new actual type
variable or a different child invocation. Old journal constraints remain and
need a full-journal model-preservation argument, not only raw snapshot freshness.
