import Yulang.GeneralDictionaryJournalRefinement228Cycles
import Yulang.GeneralDictionaryOptionalInstall229
import Yulang.GeneralDictionaryDefaultRegression208

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOptionalEnable229
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralDictionaryJournalRefinement228Cycles (Form)

abbrev sourceForm (identity : Nat) : Form :=
  if identity = 0 ∨ identity = 1 then .foo else if identity = 3 then .top else .width

theorem high_form (identity) : (modelHigh identity).1 = (sourceForm identity).value := by
  simp only [modelHigh,GeneralDictionaryJournalRefinement228Source.model,sourceForm]
  split
  · rfl
  · split <;> rename_i h
    · subst identity; rfl
    · split <;> rfl

theorem high_initial : GeneralNominalCenteredHeadMatStepJournal.Models start modelHigh :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr (source_models true)

theorem acyclic (origin) : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic start origin :=
  GeneralDictionaryJournalRefinement228Cycles.acyclic high_initial
    (fun identity => ⟨sourceForm identity,high_form identity⟩) origin

theorem raw_edge_decreases {a b : Fin 5} (edge : GeneralNominalMixedRecurrence.Edge snapshot a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 Fin.elim0 else .deferred .unresolved :
      GeneralNormalizedObservation.Head view.shapes 5) = .structural kind children at recorded
    split at recorded
    · cases recorded
      exact Fin.elim0 index
    · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound snapshot a b nominal modelHigh (source_models true)
    have observation := embed_observation modelHigh _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      rw [high_form] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child
        (sourceForm a.val) equal found
      rw [high_form] at same
      have rankEq := GeneralDictionaryJournalRefinement228Cycles.equivalent_rank child (sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 5) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path snapshot a b →
      (sourceForm b.val).rank ≤ (sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady start root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry start root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared prepared
    · exact unclosed administrative_ready

theorem selected : GeneralNominalCenteredHeadMatStepBoundary.Local registry start root
    (.selected declaration.id packet.children) := by
  refine .selected safe unique ?_
  intro conflict
  exact conflict.2 ⟨model,inhabited,⟨packet.children,unique⟩,plan,frame,ready,effect_holds⟩

theorem enabled : GeneralDictionaryDefaultKernel208.Installable registry start effect := by
  apply (GeneralNominalCenteredHeadMatCompletionLive.selected_installable_iff (effect := effect) checked legacy_reachable selected rfl rfl).mpr
  refine ⟨?_,model,inhabited,packet_holds,effect_holds⟩
  intro prior member
  cases member


theorem not_committed : ¬ GeneralDictionaryDefaultKernel208.Committed start plan := by
  intro committed
  have packet := committed.1.1 modelHigh high_initial
  have output := packet.2.2
  change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds (GeneralNominalCenteredHeadMatEffects.variables plan modelHigh) modelHigh at output
  rw [emitted_schema] at output
  have same := output ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (List.mem_singleton_self _)
  exact GeneralDictionaryOptionalOutput229.width_not_below same.1

theorem step : GeneralDictionaryDefaultKernel208.Step registry root start installed :=
  ⟨root,.root,.install effect enabled not_committed⟩

theorem high_removed : ¬ GeneralNominalCenteredHeadMatStepJournal.Models installed modelHigh := by
  intro valid
  have packet := (GeneralNominalCenteredHeadMatStepJournal.install_models (state := start) (effect := effect) rfl).mp valid |>.2.1
  have output := packet.2.2
  change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds (GeneralNominalCenteredHeadMatEffects.variables plan modelHigh) modelHigh at output
  rw [emitted_schema] at output
  have same := output ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (List.mem_singleton_self _)
  exact GeneralDictionaryOptionalOutput229.width_not_below same.1

end Yulang.GeneralDictionaryOptionalEnable229
