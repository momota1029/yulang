import Yulang.GeneralLiveCompoundRegistry316

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 22000
namespace Yulang.GeneralLiveCompoundRoot316
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryJournalRefinement228Source (roles root snapshot context)
open GeneralLiveCompoundRegistry316
open GeneralNominalVersionedCandidates231 (Prepared Failed Survivor Unique inputs InspectionPending)
open GeneralNominalRecursiveCandidates (report arguments)
open GeneralNominalRecursiveInspection

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem source_metadata : GeneralNominalRecursiveCandidates.Metadata registry context := source.metadata

theorem nominal_head : GeneralNominalVersionedPlans231.HeadModels packet GeneralDictionaryCompoundVersionedModel238.extended := by
  apply And.intro
  · apply (GeneralNominalVersionedPlans231.private_models_iff ..).mpr
    exact ((GeneralNominalVersionedPlans231.private_models_iff ..).mp
      GeneralDictionaryCompoundVersionedPacket238.head_model.1)
  · exact GeneralDictionaryCompoundVersionedPacket238.head_model.2

theorem prepared : Prepared registry context root declaration := by
  refine ⟨source_metadata,⟨source.linked.1,by intro output member; cases member⟩,
    [(0,0)],by decide +kernel,?_,?_,_,nominal_head⟩
  · intro key _ collision
    have high : 4 < GeneralNominalIdentities.source snapshot.seed key :=
      GeneralNominalIdentities.source_above_seed snapshot.seed _
    have low := GeneralDictionaryJournalRefinement228Source.source_bound _ collision
    change GeneralNominalIdentities.source snapshot.seed key ≤ 4 at low
    omega
  · change Finished (report context GeneralDictionaryCompoundSource238.declaration [(0,0)])
    rw [GeneralDictionaryCompoundPacket238.report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry initialState.core root declaration.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,rfl,
    by decide +kernel,prepared⟩

theorem survivor : Survivor registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) :=
  ⟨GeneralDictionaryCompoundPacket238.known,declaration,List.mem_cons_self,declaration_checked,
    rfl,rfl,[(0,0)],by decide +kernel,prepared,rfl⟩

theorem unique : Unique registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,eq,role,_,_,_,_⟩ := copy
  rcases List.mem_cons.mp visible with h | h
  · subst d; subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked other survivor⟩
  · cases List.mem_singleton.mp h
    change (1:Nat) = 0 at role
    cases role

noncomputable def effect : GeneralNominalVersionedJournal232.Effect roles where
  registry := registry
  snapshot := initialState.core
  plan := plan
  frame := frame
  unique := unique
  ready := GeneralDictionaryCompoundPacket238.ready

end Yulang.GeneralLiveCompoundRoot316
