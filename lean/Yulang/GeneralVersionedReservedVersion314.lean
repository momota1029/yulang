import Yulang.GeneralVersionedStoredOwnerKeys314
import Yulang.GeneralVersionedProtectedName312

set_option backward.isDefEq.respectTransparency false
/-! A positive-version raw reservation originates in the input-name keys
of one actual installation. Under that owner's stored key, it is an exact
ledger entry whenever the current aggregate multiplicity needs an equation. -/
namespace Yulang.GeneralVersionedReservedVersion314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (seed context raw)
open GeneralNominalAggregateVersion231 (key slot)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralNominalAllocation (occurrences lower upper)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralVersionedEssentialAggregates313 (Historical)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)

theorem name_key {k : Origin} (polarity : k.2.2.1 = 0 ∨ k.2.2.1 = 1)
    (member : k ∈ GeneralNominalVersionedAllocation231.declarationKeys owner d binds) :
    ∃ name ∈ d.inputNames, k = key owner d.id 0 name binds ∨ k = key owner d.id 1 name binds := by
  simp only [GeneralNominalVersionedAllocation231.declarationKeys,List.mem_append] at member
  rcases member with (input|output)|clause
  · obtain ⟨name,found,tags⟩ := List.mem_flatMap.mp input
    simp only [List.mem_cons,List.not_mem_nil,or_false] at tags
    exact ⟨name,found,tags⟩
  · obtain ⟨name,declared,rfl⟩ := List.mem_map.mp output
    exfalso; rcases polarity with h|h <;> simp [GeneralNominalAllocation.origin] at h
  · obtain ⟨c,_,within⟩ := List.mem_flatMap.mp clause
    simp only [List.mem_append,List.mem_cons] at within
    rcases within with (rfl|arguments)|outputs
    · exfalso; rcases polarity with h|h <;> simp [GeneralNominalAllocation.origin] at h
    · obtain ⟨idx,_,hit⟩ := List.mem_flatMap.mp arguments
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
      rcases hit with rfl|rfl <;> (exfalso; rcases polarity with h|h <;> simp [GeneralNominalAllocation.origin] at h)
    · obtain ⟨e,_,rfl⟩ := List.mem_map.mp outputs
      exfalso; rcases polarity with h|h <;> simp [GeneralNominalAllocation.origin] at h

theorem from_reservation {p : Packet roles} {past : Plan roles}
    (registryChecked : Checked past.packet.registry)
    (visiblePrior : past.packet.declaration ∈ past.packet.registry.declarations)
    (sameSeed : past.packet.context.state.seed = p.context.state.seed)
    (chosenKey : past.packet.declaration.id = p.declaration.id)
    (entry : GeneralNominalFiniteEquationRealization236.Entry)
    (listed : entry ∈ packetEntries p)
    (reservation : entry.1 ∈ GeneralVersionedInstallDomain313.reserve past.packet) :
    ∃ other ∈ packetEntries past.packet, other.1 = entry.1 := by
  obtain ⟨name,member,count,which⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp listed
  obtain ⟨previous,prevKey,encoded⟩ := List.mem_map.mp reservation
  obtain ⟨decl,visible,prevMember⟩ := List.mem_flatMap.mp prevKey
  have provenance (mode : Nat) (modeKnown : mode = 0 ∨ mode = 1) (known : entry.1 = slot p.context.state.seed p.site.occurrence.identity
      p.declaration.id mode name p.bindings) :
      ∃ sourceName ∈ past.packet.declaration.inputNames, (occurrences past.packet.bindings sourceName).length ≠ 1 ∧
        previous = key past.packet.site.occurrence.identity past.packet.declaration.id mode sourceName past.packet.bindings := by
    have same : previous = key p.site.occurrence.identity p.declaration.id mode name p.bindings := by
      apply (source_identity p.context.state.seed _ _).mp
      rw [← sameSeed]
      exact encoded.trans (by rw [sameSeed]; exact known)
    have tag : previous.2.2.1 = 0 ∨ previous.2.2.1 = 1 := by rw [same]; exact modeKnown
    obtain ⟨sourceName,present,keySlot | keySlot⟩ := name_key tag prevMember
    all_goals
      have eq : decl.id = p.declaration.id := by
        exact congrArg (fun o : Origin => o.2.1) (keySlot.symm.trans same)
      have packetDecl : decl = past.packet.declaration := by
        exact GeneralDictionaryEmissionPlans.declaration_key_unique _
          registryChecked _ _ visible visiblePrior (eq.trans chosenKey.symm)
      rw [packetDecl] at present keySlot
      have coordinates := keySlot.symm.trans same
      have version : (occurrences past.packet.bindings sourceName) = occurrences p.bindings name := by
        have v := congrArg (fun k : Origin => k.2.2.2.2) coordinates
        exact GeneralNominalAggregateVersion231.code_injective (Nat.succ.inj v)
      have side := congrArg (fun o : Origin => o.2.2.1) coordinates
      refine ⟨sourceName,present,version ▸ count,?_⟩
      simp only [key,GeneralNominalAllocation.origin] at side
      rw [← side]
      exact keySlot
  rcases which with lo|hi
  · obtain ⟨x,named,multi,same⟩ := provenance 0 (.inl rfl) (congrArg Prod.fst lo)
    refine ⟨(slot past.packet.context.state.seed past.packet.site.occurrence.identity past.packet.declaration.id 0 x
      past.packet.bindings, lower (occurrences past.packet.bindings x)),?_,?_⟩
    · exact (GeneralNominalVersionedAggregateRealization236.member_iff ..).mpr ⟨x,named,multi,.inl rfl⟩
    · exact (congrArg (source past.packet.context.state.seed) same).symm.trans encoded
  · obtain ⟨x,named,multi,same⟩ := provenance 1 (.inr rfl) (congrArg Prod.fst hi)
    refine ⟨(slot past.packet.context.state.seed past.packet.site.occurrence.identity past.packet.declaration.id 1 x
      past.packet.bindings, upper (occurrences past.packet.bindings x)),?_,?_⟩
    · exact (GeneralNominalVersionedAggregateRealization236.member_iff ..).mpr ⟨x,named,multi,.inr rfl⟩
    · exact (congrArg (source past.packet.context.state.seed) same).symm.trans encoded


theorem raw_history {s : State roles} {p : Packet roles}
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (actual : Reachable registry root s) (aligned : p.context = context s)
    (keyConsistent : ∀ prev ∈ s.plans, prev.packet.site.occurrence.identity = p.site.occurrence.identity →
      prev.packet.declaration.id = p.declaration.id)
    (entry : GeneralNominalFiniteEquationRealization236.Entry)
    (listed : entry ∈ packetEntries p) (current : entry.1 ∈ raw s) :
    Historical s entry.1 := by
  obtain ⟨versioned,owns,code,_⟩ := GeneralVersionedNewOwnerHead314.entry_address listed
  have matching : source (seed s) versioned = entry.1 := by rw [aligned] at code; exact code
  rcases GeneralVersionedTraceDomain313.reached actual _ (List.mem_append_left _ current) with small | ⟨p0,stored,reserved⟩
  · exact False.elim (Nat.not_lt_of_ge (matching.symm ▸ small) (source_above_seed _ _))
  · have priorSeed : p0.packet.context.state.seed = seed s :=
      GeneralNominalVersionedMixedSeedLedger237.reachable actual p0 stored
    have sameSeed : p0.packet.context.state.seed = p.context.state.seed := by rw [aligned]; exact priorSeed
    have reserveId : source p0.packet.context.state.seed versioned = entry.1 := by rw [priorSeed]; exact matching
    have owner := GeneralVersionedInstallDomain313.reserve_owner p0.packet (reserveId.symm ▸ reserved)
    have sameKey := keyConsistent p0 stored (owner.symm.trans owns)
    have compiledId := (GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 p0 stored
    have legal : Checked p0.packet.registry := compiledId.symm ▸
      (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
    obtain ⟨e,hist,planEq⟩ := GeneralVersionedSiteOrigins312.stored_effect actual stored
    have visible : p0.packet.declaration ∈ p0.packet.registry.declarations := by
      rw [← planEq]
      exact e.frame.registry_eq ▸ e.frame.visible
    obtain ⟨old,read,same⟩ := from_reservation legal visible sameSeed sameKey entry listed reserved
    exact ⟨p0,stored,old,read,same⟩

theorem snapshot_coverage {s : State roles} {p : Packet roles}
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (actual : Reachable registry root s) (aligned : p.context = context s)
    (keyConsistent : ∀ prev ∈ s.plans, prev.packet.site.occurrence.identity = p.site.occurrence.identity →
      prev.packet.declaration.id = p.declaration.id) :
    IdCovered (GeneralVersionedProtectedPeer312.semanticPool p) s p := by
  intro entry listed footprint
  have inRaw := GeneralNominalSemanticRawFrame236.contained p.context.state footprint
  rw [aligned] at inRaw
  exact raw_history checked actual aligned keyConsistent entry listed inRaw

end Yulang.GeneralVersionedReservedVersion314
