import Yulang.GeneralWhereVersionInstall317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 47000000
namespace Yulang.GeneralWhereVersionJournal317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralWhereVersionCase317 (site)
open GeneralWhereVersionCommit317 (core framedState requests_iff)
open GeneralWhereVersionInstall317 (fixed before mixed_eq models)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralWhereVersionRefine317 (restrict)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem prior (m : Assignment) (valid : Models framedState m) : Models after m := by
  refine ⟨⟨restrict m valid.1.1,valid.1.2.1,?_,?_,valid.1.2.2.2.2.1,?_⟩,valid.2.1,?_⟩
  · intro raw member
    exact valid.1.2.2.1 raw (List.mem_append_left _ member)
  · intro before member
    exact valid.1.2.2.2.1 before (List.mem_append_left _ member)
  · intro e member
    have too := valid.1.2.2.2.2.2 e member
    exact ⟨too.1,GeneralNominalCenteredHeadMatEffects.restrict
      (fun out shown => (requests_iff _ _).mpr shown) too.2⟩
  · intro e member
    have too := valid.2.2 e member
    exact ⟨too.1,GeneralNominalVersionedJournal232.live_restrict
      (fun out shown => (requests_iff _ _).mpr shown) too.2⟩

theorem fixed_iff (m : Assignment) : GeneralWhereVersionInstall317.Models fixed m ↔ ParentHolds m := by
  constructor
  · intro valid
    have mixed : Models framedState m := mixed_eq ▸ valid.1
    obtain ⟨holds,classes⟩ := valid.2 rootPlan (List.mem_singleton_self _)
    have current : GeneralNominalVersionedEffects231.ClassEffects core root rootPlan m := by
      rw [mixed_eq] at classes
      exact classes
    refine ⟨prior m mixed,holds.head,holds.headSchema,?_,holds.rows⟩
    exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun out => requests_iff root out)).mp current
  · exact models m

end Yulang.GeneralWhereVersionJournal317
