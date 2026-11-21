import Yulang.GeneralVersionedReservedVersion314
import Yulang.GeneralVersionedAliasChoice312

set_option backward.isDefEq.respectTransparency false
/-! A historical choice at the current numeric invocation remains prepared
under arbitrary actual intervening refreshes, merges and installations, if
a checked source candidate is currently selected and its full state models.
Same-owner declaration agreement is a result, not a current key premise. -/
namespace Yulang.GeneralVersionedSameOwnerChoice314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
  {s : State roles} {prior : Packet roles}

theorem covered
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (member : prior ∈ s.core.erased.current.packets)
    (same : prior.site.occurrence.identity = focus.identity) :
    GeneralVersionedAliasChoice312.Coverage registry s focus prior.declaration := by
  obtain ⟨old,present,rfl⟩ := GeneralNominalVersionedMixedChoiceHistory236.packet_plan actual member
  intro cert bounds _
  apply GeneralVersionedReservedVersion314.snapshot_coverage checked actual rfl
  intro p found own
  exact GeneralVersionedStoredOwnerKeys314.reached actual p found old present (own.trans same.symm)

theorem prepared
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected k kids))
    (valid : Models s m)
    (member : prior ∈ s.core.erased.current.packets)
    (same : prior.site.occurrence.identity = focus.identity) :
    Prepared (Compiled registry) s.core.erased.current.context focus prior.declaration := by
  have alias : Alias s.core.erased.current focus.identity prior.site.occurrence.identity :=
    same.symm ▸ Alias.refl _
  exact GeneralVersionedHistoricalTransport312.prepared checked actual selected valid member alias
    (GeneralVersionedAliasChoice312.transfer checked actual selected valid member alias
      (covered checked actual member same))

theorem key_eq
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected k kids))
    (valid : Models s m)
    (member : prior ∈ s.core.erased.current.packets)
    (same : prior.site.occurrence.identity = focus.identity) :
    prior.declaration.id = k := by
  have alias : Alias s.core.erased.current focus.identity prior.site.occurrence.identity :=
    same.symm ▸ Alias.refl _
  have compiled := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
  exact (GeneralNominalVersionedMixedChoice236.prepared_iff_key compiled.1 compiled.2 focus unique
    (GeneralNominalVersionedMixedChoiceHistory236.visible actual member)).mp
    ⟨GeneralNominalVersionedMixedChoiceHistory236.historical_role checked actual selected member alias,
      prepared checked actual selected valid member same⟩

end Yulang.GeneralVersionedSameOwnerChoice314
