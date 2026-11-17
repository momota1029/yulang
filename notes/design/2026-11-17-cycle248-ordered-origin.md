# Cycle248: actual origin transport under ordered definition readback

Implement GeneralNominalOrderedOrigin248 against actual OriginView243, not a
replacement observation semantics. Exact mapping read = sequential solve and
compile/subst observation iff need no SafeOrder. Compatible assignments give
an Equivalent witness for arbitrary origins; nominal/structural outer paths
retain the same actual witness by transporting only their parent observation.
Source leaves do not in general retain a literal syntax representative.

Actual Test.Holds is equivalence-stable for scalar, structural and nominal
constructors. Thus Head and Same are invariant under Compatible assignments,
including source leaves. Ordered rebase combines these with old SafeOrder,
fresh targets within old targets, and satisfaction of the old block. Fresh
SafeOrder is unnecessary for observation transport alone, but remains needed
in the separate fresh-block-model existence theorem.

No actual metadata coverage, operational-law producer, source reachability,
termination, or EvidenceNode claim is made. Current/history/cache and report
bounds require a common-model field adapter beyond this file. No older Lean
source is edited. Verification is pending the parent's bounded dependency
cache preparation; this note does not claim a completed build.

## Bounded next connection (read-only review)

Existing `GeneralNominalAssignmentCongruence238.Same` is definitionally the
concrete Common instance of ModelCongruence245.Compatible. Existing
`GeneralNominalProjectionCongruence238.projection_iff` and
`GeneralNominalVersionedPacketCongruence238.holds_iff` therefore accept the
ordered solve recovery relation without a new stability premise.

For state/report, `ProjectionView243.compile_exact` instantiated with
`mapping old` at `solve fresh rho`, followed by read_mapping, solve_absorbs,
and projection_iff, yields the original actual ProjectionModels at rho iff
compiled report Models at the fresh extension. The analogous composition of
`PacketView243.compile_exact` and VersionedPacketCongruence238.holds_iff yields
actual VersionedPlans231.Holds iff compiled Packet.Holds. Both require old
SafeOrder, fresh TargetsWithin old, and old block satisfaction. Fresh safety
is separate from these transport facts. The packet compiler explicitly covers
raw/ordinary/projection/input/binders/head/children/outputs fields.

This covers compiled actual report/packet values, not arbitrary compiled-view
substitution or all current/history/cache occurrences. No replacement source
semantics, source ordering producer, or final transition has been chosen.

## Verified first result and packet implementation scope

GeneralNominalOrderedOrigin248 passed the focused Lean --trust=0 build with
exit 0 and no warnings in the cycle247-clean dependency cache. All originally
planned origin theorems are present, including nominal/structural rebase and
Head/Same rebase. This verification does not turn the remaining source
ordering and metadata coverage boundaries into proved claims.

GeneralNominalOrderedPacket248 is now implemented, awaiting its dependency
cache and focused verification. It provides exact evaluation (arbitrary
entries), recovery (old block Models, no SafeOrder), fresh rebase (old
SafeOrder and fresh target inclusion), and finite-list simultaneous packet
transport at one common model assignment. The list theorem quantifies over a
supplied list of actual Plans; it does not assert a complete journal listing.
No fresh SafeOrder is used by these transport facts: that condition belongs
to separately proving the fresh block has been satisfied.

## Verified packet result and single-witness composition

GeneralNominalOrderedPacket248 passed the focused --trust=0
-DwarningAsError=true build without changes or warnings. The preceding
"awaiting verification" statement records the earlier stage only.

GeneralNominalOrderedPacketModels248 also passed that strict build. Its
models_forward/models_backward/public_models_iff combine a finite list of
actual Plans with arbitrary Presence consumer atoms, old/fresh block equations
and public Agrees in ONE existential assignment on each side. Forward uses
solve fresh; backward uses solve old. Thus packet truths are not certified
using separate unrelated private witnesses. No new packet stability premise
is assumed: actual 238 congruence and 243 compiler exactness supply it.

This does not discharge the choice of public coordinates: promoted source
names cannot be hidden merely by calling old targets private. Nor does the
supplied finite Plan list establish complete metadata enumeration or a
successor transition. The actual refreshed entry producer, source ordering,
scheduler/progress and unconditional EvidenceNode remain separate obligations.
