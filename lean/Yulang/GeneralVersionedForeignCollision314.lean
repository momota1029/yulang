import Yulang.GeneralVersionedRemainingWrites314

set_option backward.isDefEq.respectTransparency false
/-! A failing historical alias is not explained by candidate enumeration,
old read-list inequality, or fresh names. It requires a real non-singleton
target of the reinspection, semantically read at the live snapshot, with
the exact address previously reserved under a different installed key. -/
namespace Yulang.GeneralVersionedForeignCollision314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralVersionedEssentialAggregates313 (Historical)
open GeneralVersionedPeerChoice311 (reads)
open GeneralVersionedHistoricalTransport312 (atFocus)
open GeneralVersionedProtectedPeer312 (semanticPool)
open GeneralVersionedTraceDomain313 (seed context raw)
open GeneralNominalIdentities (source source_above_seed)
open GeneralVersionedInstallDomain313 (reserve)

def Collision (registry : Registry) (s : State roles) (focus : Occurrence roles)
    (old : Declaration) (selectedKey : Nat) : Prop :=
  ∃ checked : DeclarationChecked (Compiled registry).constructors roles old,
  ∃ bounds, reads (context s) focus = some bounds ∧
    let p := atFocus s registry focus old checked bounds
    ∃ row ∈ packetEntries p, row.1 ∈ semanticPool p ∧ ¬ Historical s row.1 ∧
      ∃ producer ∈ s.plans,
        producer.packet.site.occurrence.identity = focus.identity ∧
        producer.packet.declaration.id = selectedKey ∧ row.1 ∈ reserve producer.packet

theorem wrong_key {s : State roles} {old : Packet roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s focus (.selected key kids))
    (valid : Models s m) (present : old ∈ s.core.erased.current.packets)
    (alias : Alias s.core.erased.current focus.identity old.site.occurrence.identity)
    (different : old.declaration.id ≠ key) :
    old.site.occurrence.identity ≠ focus.identity ∧ Collision registry s focus old.declaration key := by
  classical
  have foreign : old.site.occurrence.identity ≠ focus.identity :=
    fun same => different (GeneralVersionedSameOwnerChoice314.key_eq checked actual selected valid present same)
  refine ⟨foreign,?_⟩
  have compile := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
  have oldVisible := GeneralNominalVersionedMixedChoiceHistory236.visible actual present
  have role := GeneralNominalVersionedMixedChoiceHistory236.historical_role checked actual selected present alias
  have noCoverage : ¬ GeneralVersionedAliasChoice312.Coverage registry s focus old.declaration := by
    intro covered
    have prepared := GeneralVersionedHistoricalTransport312.prepared checked actual selected valid present alias
      (GeneralVersionedAliasChoice312.transfer checked actual selected valid present alias covered)
    exact different ((GeneralNominalVersionedMixedChoice236.prepared_iff_key
      compile.1 compile.2 focus unique oldVisible).mp ⟨role,prepared⟩)
  have unsatisfied :
      ∃ proof : DeclarationChecked (Compiled registry).constructors roles old.declaration,
      ∃ bounds, reads (context s) focus = some bounds ∧
        let p := atFocus s registry focus old.declaration proof bounds
        ∃ row ∈ packetEntries p, row.1 ∈ semanticPool p ∧ ¬ Historical s row.1 := by
    apply Classical.byContradiction
    intro absent
    apply noCoverage
    intro proof bounds located
    dsimp only
    intro row listed semantic
    apply Classical.byContradiction
    intro unrecorded
    exact absent ⟨proof,bounds,located,row,listed,semantic,unrecorded⟩
  obtain ⟨proof,bounds,located,row,listed,semantic,notInLedger⟩ := unsatisfied
  refine ⟨proof,bounds,located,row,listed,semantic,notInLedger,?_⟩
  let p := atFocus s registry focus old.declaration proof bounds
  obtain ⟨origin,owner,address,_⟩ := GeneralVersionedNewOwnerHead314.entry_address (p := p) listed
  have fromRaw : row.1 ∈ raw s := GeneralNominalSemanticRawFrame236.contained _ semantic
  rcases GeneralVersionedTraceDomain313.reached actual _ (List.mem_append_left _ fromRaw) with low|⟨prior,stored,reserved⟩
  · exact False.elim (Nat.not_lt_of_ge (address.symm ▸ low) (source_above_seed _ _))
  · have proofSeed : prior.packet.context.state.seed = seed s :=
      GeneralNominalVersionedMixedSeedLedger237.reachable actual prior stored
    change source (seed s) origin = row.1 at address
    have reservedId : source prior.packet.context.state.seed origin ∈ reserve prior.packet := by
      rw [proofSeed,address]
      exact reserved
    have same : prior.packet.site.occurrence.identity = focus.identity :=
      (GeneralVersionedInstallDomain313.reserve_owner prior.packet reservedId).symm.trans owner
    have oldRecord : prior.packet ∈ s.core.erased.current.packets := by
      rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
      exact List.mem_map.mpr ⟨prior,stored,rfl⟩
    exact ⟨prior,stored,same,GeneralVersionedSameOwnerChoice314.key_eq checked actual selected valid oldRecord same,reserved⟩

theorem choice_if_no_collision {s : State roles} {p : Packet roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (selected : Local registry s p.site.occurrence (.selected p.declaration.id kids))
    (valid : Models s m)
    (exclude : ∀ old ∈ s.core.erased.current.packets,
      Alias s.core.erased.current p.site.occurrence.identity old.site.occurrence.identity →
      ¬ Collision registry s p.site.occurrence old.declaration p.declaration.id) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current p := by
  classical
  intro old present alias
  apply Classical.byContradiction
  intro diff
  exact exclude old present alias (wrong_key checked actual selected valid present alias (Ne.symm diff)).2

end Yulang.GeneralVersionedForeignCollision314
