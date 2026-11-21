import Yulang.GeneralLiveCompoundChildSite316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralLiveCompoundLeafHead316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot lower_width)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry leaf leaf_checked source)
open GeneralLiveCompoundUpperRefresh316 (upperState old_models)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundChildSite316
open GeneralSourceDictionaries GeneralNominalCenters GeneralDeclarations
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedCandidates231
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalOriginTerms (Same Head)
open CommonNominalFullCarrier

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,childSite.observed,leaf,leaf_checked,[(5,6)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,childSite,rfl⟩

theorem bindings : packet.bindings = [(0,4,2)] := by
  change GeneralNominalRecursiveInspection.bindings snap
    (GeneralNominalRecursiveCandidates.report context leaf [(5,6)]) = _
  rw [leaf_report]
  rfl

theorem ordinary (m : Assignment) (valid : Models upperState m) : Ordinary packet m := by
  have old := (old_models m).mp valid
  have low := lower_width m old.1.2.1
  have childBounds := old.1.2.2.2.1 GeneralDictionaryCompoundSites238.childSite
    (GeneralMixedCompoundUpperHalt307.centers ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _)) 0
  refine ⟨?_,?_,?_⟩
  · rw [bindings]
    apply (GeneralNominalAllocation.cross_exact ..).mp
    intro atom member
    simp [GeneralNominalAllocation.cross] at member
    rcases member with rfl
    exact low
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [bindings]
    exact PresenceNormalForm.all_nil _ _
  · change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (selfChecks snap (GeneralNominalRecursiveCandidates.report context leaf [(5,6)]))
    rw [leaf_report]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact subtype_trans childBounds.1 childBounds.2
    · exact subtype_trans childBounds.1 childBounds.2
    · exact low

theorem projection_empty (m : Assignment) :
    ProjectionModels snap (GeneralNominalPacketSupport.report packet) m := by
  change ProjectionModels snap (GeneralNominalRecursiveCandidates.report context leaf [(5,6)]) m
  rw [leaf_report]
  refine ⟨(fun _ h => nomatch h),(fun _ h => nomatch h),?_,?_⟩
  · intro first present
    cases List.mem_singleton.mp present
    intro _ _ _ _ absent; cases absent
  · intro first present
    cases List.mem_singleton.mp present
    intro _ _ _ _ _ absent; cases absent

theorem head (m : Assignment) (valid : Models upperState m) : HeadModels packet m :=
  ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨valid.1.1,ordinary m valid⟩,projection_empty m⟩

end Yulang.GeneralLiveCompoundLeafHead316
