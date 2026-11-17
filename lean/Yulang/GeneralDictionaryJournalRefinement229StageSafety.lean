import Yulang.GeneralDictionaryJournalRefinement229Cycles
import Yulang.GeneralDictionaryJournalRefinement228RawStage
import Yulang.GeneralDictionaryJournalRefinement228Enable
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement229StageSafety
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralDictionaryJournalRefinement228Stage
open GeneralDictionaryJournalRefinement228RawStage
open GeneralDictionaryJournalRefinement229Cycles
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev current := GeneralDictionaryJournalRefinement228Current.currentContext allocated reserved ordinary
abbrev sourceForm (identity : Nat) : Form :=
  if identity ≤ 4 then
    if identity = 0 ∨ identity = 1 then .foo else if identity = 2 then .width else if identity = 3 then .top else .exact
  else if identity = lo then .exact else .width

theorem model_form (identity) : (model identity).1 = (sourceForm identity).value := by
  simp only [GeneralDictionaryJournalRefinement228Install.model,sourceForm]
  split
  · simp only [modelLow,GeneralDictionaryJournalRefinement228Source.model]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · split <;> rfl

theorem acyclic (origin) : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic stage origin :=
  GeneralDictionaryJournalRefinement229Cycles.acyclic stage_model
    (fun identity => ⟨sourceForm identity,model_form identity⟩) origin

theorem raw_edge_decreases {a b : Fin 5} (edge : GeneralNominalMixedRecurrence.Edge current.state a b) :
    (GeneralDictionaryJournalRefinement228Enable.sourceForm b.val).rank <
      (GeneralDictionaryJournalRefinement228Enable.sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head view.shapes 5) = .structural kind children at recorded
    split at recorded
    · cases recorded
      exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound current.state a b nominal modelHigh current_raw
    have observation := embed_observation modelHigh _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      rw [GeneralDictionaryJournalRefinement228Enable.high_form] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child
        (GeneralDictionaryJournalRefinement228Enable.sourceForm a.val) equal found
      rw [GeneralDictionaryJournalRefinement228Enable.high_form] at same
      have rankEq := GeneralDictionaryJournalRefinement228Cycles.equivalent_rank child
        (GeneralDictionaryJournalRefinement228Enable.sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 5) : ¬ GeneralNominalCycleK2.RecursAt current.state slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path current.state a b →
      (GeneralDictionaryJournalRefinement228Enable.sourceForm b.val).rank ≤
      (GeneralDictionaryJournalRefinement228Enable.sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady stage root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
  exact .refl _

theorem known : ¬ GeneralNominalState.RootPending current.state
    (GeneralNominalCenteredHeadCandidates.inputs root).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 5),rfl,Or.inr ⟨GeneralDictionaryJournalRefinement228Reobserve.exactCopy,rfl⟩⟩

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry stage root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared current_prepared
    · exact unclosed administrative_ready
end Yulang.GeneralDictionaryJournalRefinement229StageSafety
