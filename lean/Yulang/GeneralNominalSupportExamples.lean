import Yulang.GeneralNominalSupportGrowth
import Yulang.GeneralNominalSaturationExamples
import Yulang.GeneralNominalSupportInstallation

/-! Source-supported Display and Wrap retain their general nominal survivors,
children and support certificates. The list constructor is nominal throughout. -/
namespace Yulang.GeneralNominalSupportExamples

open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarations
open GeneralDeclarationExamples (roles display wrap display_checked wrap_checked)
open GeneralNominalExamples

abbrev start (root : Occurrence roles) : Tracked roles := GeneralNominalSupport.initial (context true) root

private theorem all_heads (slot : Fin (state true).base.slots) :
    ∃ test observation, Head (state true) ((state true).base.source slot) test observation := by
  have bounded := slot.isLt
  change slot.val < 2 at bounded
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by
      apply Fin.ext
      change slot.val = 1
      omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl⟩

private theorem roots (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    Roots (start root) [] root := by
  intro index
  rw [show (root.demand.arguments index).1 = 0 by rw [arguments index]]
  exact source_ready (start root) 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := state true) 0 listDescriptor rfl) (Head.nominal (snapshot := state true) 0 listDescriptor rfl) []

theorem all_source_decisions (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    DecisionGuard (start root) registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),roots root arguments,?_⟩
  intro declaration visible role bounds located slot member
  obtain ⟨test,observation,head⟩ := all_heads slot
  exact source_ready (start root) _ test observation observation head head []

theorem display_guard : PacketGuard (start displayRoot)
    ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,display,display_checked,[(0,0)]⟩ [] := by
  have decisions := all_source_decisions displayRoot (fun _ => rfl)
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 display (by simp) rfl _ (by decide +kernel)⟩,decisions⟩

theorem wrap_guard : PacketGuard (start wrapRoot)
    ⟨registry,context true,GeneralNominalDemandMerging.pointSite wrapRoot,wrap,wrap_checked,[(0,0)]⟩ [] := by
  have decisions := all_source_decisions wrapRoot (fun _ => rfl)
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 wrap (by simp) rfl _ (by decide +kernel)⟩,decisions⟩

theorem display_exactly_one (key : Nat) (children : List (Occurrence roles)) :
    (GeneralNominalSupportBoundary.boundary roles).Survivor registry (start displayRoot) displayRoot key children ↔
      key = 1 ∧ children = [displayChild] := GeneralNominalRecursiveRegressions.display_exactly_one key children

theorem wrap_child_equation :
    (GeneralNominalSupportBoundary.boundary roles).Survivor registry (start wrapRoot) wrapRoot 2 [wrapChild] ∧
      wrapChild.demand.outputs = [⟨1,itemTarget⟩] ∧
      ¬ GeneralNominalSupportBoundary.SupportPending registry (start wrapRoot) wrapRoot :=
  ⟨GeneralNominalRecursiveExamples.wrap_survivor,rfl,fun pending => pending ⟨[],all_source_decisions wrapRoot (fun _ => rfl)⟩⟩

theorem emitted_inputs_source_supported : Roots (start displayRoot) [] displayChild ∧ Roots (start wrapRoot) [] wrapChild := by
  constructor <;> intro index <;>
    exact source_ready _ 1 (.scalar .int) _ _ (Head.scalar (snapshot := state true) 1 .int rfl) (Head.scalar (snapshot := state true) 1 .int rfl) []

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem raw_acyclic (slot : Fin (state true).base.slots) : ¬ GeneralNominalCycleK2.Cycle (state true) slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge (state true) first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model (state_models true)
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path (state true) first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin (state true).base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (state true) slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_feedback_cycle (root : Occurrence roles) (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle (start root).current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model ((initial_models ..).mpr (state_models true))
    height model_height (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

private theorem no_root (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.RootK2 (start root).current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact no_feedback_cycle root _ cycle

private theorem no_candidate (root : Occurrence roles) :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry (start root).current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact no_feedback_cycle root _ cycle

theorem display_selected : GeneralNominalSupportBoundary.Local registry (start displayRoot) displayRoot
    (.selected 1 [displayChild]) := by
  apply GeneralNominalSupportBoundary.selected_supported (support := []) _ (all_source_decisions displayRoot (fun _ => rfl))
  cases GeneralNominalSaturationExamples.display_selected with
  | selected safe unique =>
    refine .selected ⟨safe.1,no_root _,no_candidate _,?_⟩ unique
    rintro (old | ⟨_,legacy⟩)
    · exact safe.2.2.2 old
    · rcases legacy with root | candidate
      · exact safe.2.1 root.1
      · exact safe.2.2.1 candidate.1

private theorem wrap_prepared : GeneralNominalRecursiveCandidates.Prepared registry (context true) wrapRoot wrap wrap_checked := by
  obtain ⟨_,candidate,visible,checked,_,role,_,_,prepared,_⟩ := GeneralNominalRecursiveExamples.wrap_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases role
  · cases role
  · exact prepared

theorem wrap_selected : GeneralNominalSupportBoundary.Local registry (start wrapRoot) wrapRoot
    (.selected 2 [wrapChild]) := by
  apply GeneralNominalSupportBoundary.selected_supported (support := []) _ (all_source_decisions wrapRoot (fun _ => rfl))
  refine .selected ⟨GeneralNominalRecursiveExamples.wrap_survivor.1,no_root _,no_candidate _,?_⟩
    ⟨GeneralNominalRecursiveExamples.wrap_survivor,?_⟩
  · rintro (old | ⟨_,legacy⟩)
    · obtain ⟨_,candidate,visible,checked,role,_,absent⟩ := old
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl | rfl
      · cases role
      · cases role
      · exact absent wrap_prepared
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
  · intro key children found
    have original := found
    obtain ⟨_,candidate,visible,checked,identity,role,_⟩ := found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · cases role
    · cases role
    · have equal : key = 2 := identity.symm
      subst key
      exact ⟨rfl,GeneralNominalRecursiveCandidates.survivor_children_functional registry registry_checked
        (context true) wrapRoot 2 children [wrapChild] original GeneralNominalRecursiveExamples.wrap_survivor⟩

theorem display_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = displayRoot ∧ packet.declaration.id = 1 ∧ packet.children = [displayChild] ∧
    Step registry displayRoot (start displayRoot) (GeneralNominalSupportSteps.install (start displayRoot) packet support) :=
  GeneralNominalSupportInstallation.initial_selected_installation registry (context true) displayRoot 1 [displayChild]
    display_selected (by simp)

theorem wrap_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = wrapRoot ∧ packet.declaration.id = 2 ∧ packet.children = [wrapChild] ∧
    Step registry wrapRoot (start wrapRoot) (GeneralNominalSupportSteps.install (start wrapRoot) packet support) :=
  GeneralNominalSupportInstallation.initial_selected_installation registry (context true) wrapRoot 2 [wrapChild]
    wrap_selected (by simp)

end Yulang.GeneralNominalSupportExamples
