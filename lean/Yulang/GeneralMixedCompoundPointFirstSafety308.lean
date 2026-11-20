import Yulang.GeneralMixedCompoundPointFirstPlan308
import Yulang.GeneralDictionaryOptionalEnable229

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundPointFirstSafety308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot modelHigh source_models view)
open GeneralDictionaryJournalRefinement228Cycles (nominal_child equivalent_rank)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundFrame238 (before)
open GeneralMixedCompoundSourcePrefix308 (pointBefore reobserve_models)
open GeneralMixedCompoundPointFirstPlan308 (ctx pkt plan effect frame prepared known)
open GeneralDictionaryOptionalEnable229 (sourceForm high_form)
open GeneralNominalCenteredSteps (inspection)
open GeneralNominalRecursiveInspection (Origin)
open CommonNominalFullCarrier

theorem raw_high : GeneralNominalState.Models ctx.state modelHigh :=
  (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff _).mpr (source_models true)

theorem raw_edge {a b : Fin 5} (edge : GeneralNominalMixedRecurrence.Edge ctx.state a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
  rcases edge with structural | semantic
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head view.shapes 5) = .structural kind children at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound ctx.state a b semantic modelHigh raw_high
    have obs := GeneralNominalRecursiveInspection.embed_observation modelHigh _ actual seen
    cases obs with
    | nominal parent equal found =>
      cases parent
      rw [high_form] at equal
      obtain ⟨child,smaller,meaning⟩ := nominal_child (sourceForm a.val) equal found
      rw [high_form] at same
      have rankEq := equivalent_rank child (sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

private theorem path_order (state : GeneralNominalState.State) (rank : Fin state.base.slots → Nat)
    (fall : ∀ {a b}, GeneralNominalMixedRecurrence.Edge state a b → rank b < rank a)
    {a b : Fin state.base.slots} (path : GeneralNominalMixedRecurrence.Path state a b) : rank b ≤ rank a := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (fall edge))

theorem no_raw_cycle (slot : Fin 5) : ¬ GeneralNominalCycleK2.RecursAt ctx.state slot := by
  intro h
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ h
  have a := raw_edge edge
  have b := path_order ctx.state (fun i => (sourceForm i.val).rank) raw_edge path
  omega

theorem no_semantic_cycle (origin : Origin) : ¬ GeneralNominalVersionedCycles232.Cyclic pointBefore origin := by
  have modelEq : GeneralNominalVersionedJournal232.Models pointBefore = GeneralNominalVersionedJournal232.Models before :=
    funext (fun m => propext (reobserve_models m))
  exact fun more => GeneralDictionaryCompoundStep238.acyclic origin
    ((GeneralNominalVersionedCycles232.full_models_only modelEq).mp more)

theorem ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady pointBefore root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro a x _ b y _
  cases List.mem_singleton.mp x
  cases List.mem_singleton.mp y
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry pointBefore root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact no_raw_cycle slot cycle
    · exact no_semantic_cycle _ cycle
    · exact no_semantic_cycle _ cycle
  · rintro (raw | ⟨p,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact no_raw_cycle visited.1 cycle
    · exact no_semantic_cycle _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | pending)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact pending ready

theorem positions : GeneralNominalVersionedCycles232.Safe pointBefore plan := by
  refine ⟨?_,fun entry _ => no_semantic_cycle entry.1⟩
  decide +kernel

theorem alternatives : GeneralNominalVersionedMixedKernel234.AlternativesSafe registry pointBefore plan.input := by
  intro proposed _ framed
  have same := GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl rfl rfl framed frame
  subst proposed
  exact positions

end Yulang.GeneralMixedCompoundPointFirstSafety308
