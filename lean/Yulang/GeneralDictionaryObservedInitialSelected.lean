import Yulang.GeneralDictionaryObservedInitialExample
import Yulang.GeneralNominalSupportExamples

namespace Yulang.GeneralDictionaryObservedInitialSelected
open GeneralDictionaryObservedInitialExample
open GeneralNominalExamples (model listDescriptor)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSupport GeneralNominalSaturationState

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem raw_acyclic (slot : Fin source.base.slots) : ¬ GeneralNominalCycleK2.Cycle source slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge source first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model source_models
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path source first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin source.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt source slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_feedback_cycle (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle start.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model GeneralDictionaryObservedInitialExample.initial_models
    height model_height (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact no_feedback_cycle _ cycle

theorem no_candidate :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact no_feedback_cycle _ cycle


theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id children := by
  refine ⟨survivor,?_⟩
  rintro key kids ⟨_,decl,visible,check,identity,_,bounds,located,ready,emitted⟩
  have same := List.mem_singleton.mp visible
  subst decl
  have same : ([(0,0)] : List (Fin 2 × Fin 2)) = bounds := Option.some.inj located
  subst bounds
  exact ⟨identity.symm,emitted⟩

theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id children) := by
  refine .selected ⟨root_ready,no_root,no_candidate,?_⟩ unique
  rintro (old | ⟨_,legacy⟩)
  · obtain ⟨_,decl,visible,check,_,_,absent⟩ := old
    have same := List.mem_singleton.mp visible
    subst decl
    exact absent prepared
  · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind

theorem decisions : DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact source_ready start 0 (.nominal 0 1) _ _
      (Head.nominal (snapshot := source) 0 listDescriptor rfl)
      (Head.nominal (snapshot := source) 0 listDescriptor rfl) []
  · intro decl visible role bounds located slot member
    have bounded := slot.isLt
    change slot.val < 2 at bounded
    by_cases zero : slot.val = 0
    · have same : slot = (0 : Fin 2) := Fin.ext zero
      subst slot
      exact source_ready start 0 (.nominal 0 1) _ _
        (Head.nominal (snapshot := source) 0 listDescriptor rfl)
        (Head.nominal (snapshot := source) 0 listDescriptor rfl) []
    · have same : slot = (1 : Fin 2) := by apply Fin.ext; change slot.val = 1; omega
      subst slot
      exact source_ready start 1 (.scalar .int) _ _
        (Head.scalar (snapshot := source) 1 .int rfl)
        (Head.scalar (snapshot := source) 1 .int rfl) []

theorem support_selected : GeneralNominalSupportBoundary.Local registry start root
    (.selected declaration.id children) :=
  GeneralNominalSupportBoundary.selected_supported selected [] decisions
end Yulang.GeneralDictionaryObservedInitialSelected
