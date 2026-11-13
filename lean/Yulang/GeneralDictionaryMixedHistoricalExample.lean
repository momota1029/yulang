import Yulang.GeneralDictionaryMixedHistoricalCoverage
import Yulang.GeneralDictionaryValueRecordedCoverageLimit
import Yulang.GeneralDictionaryUnrecordedAliasLeafExample

/-! A concrete two-node Value classifier combines an actual historical nominal
root with a generated current scalar leaf which has no journal packet. -/
namespace Yulang.GeneralDictionaryMixedHistoricalExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralDictionaryValueRecordedCoverageLimit (reachable stable)

private theorem all_heads (slot : Fin 2) :
    ∃ test observation, GeneralNominalSupport.Head (state true) ((state true).base.source slot) test observation ∧
      GeneralNominalSupport.Head current.state (current.state.base.source slot) test observation := by
  have bounded := slot.isLt
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl,GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl,GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl⟩

private theorem guard (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSupport.DecisionGuard finish registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    rw [show (root.demand.arguments index).1 = slot.val by rw [args index]]
    obtain ⟨test,observation,source,seen⟩ := all_heads slot
    exact GeneralNominalSupport.source_ready finish slot.val test observation observation source seen []
  · intro declaration visible role bounds located read member
    obtain ⟨test,observation,source,seen⟩ := all_heads read
    exact GeneralNominalSupport.source_ready finish read.val test observation observation source seen []

theorem root_selected : GeneralNominalValueBoundary.Local registry finish displayRoot (.selected 1 [displayChild]) :=
  GeneralNominalValueBoundary.selected_supported parent_selected []
    (GeneralNominalValueSupport.source_decision registry finish displayRoot (guard displayRoot 0 (fun _ => rfl)))

theorem fragment : GeneralDictionaryScalarRegistryIntervals.ScalarVariableRegistry registry finish.current.context.interpretation := by
  intro d visible c required p member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases required
  · have eq := List.mem_singleton.mp required; subst c
    have eq := List.mem_singleton.mp member; subst p
    exact Or.inl ⟨0,rfl⟩
  · have eq := List.mem_singleton.mp required; subst c
    have eq := List.mem_singleton.mp member; subst p
    exact Or.inl ⟨0,rfl⟩

theorem root_supported : GeneralDictionaryHistoricalNominalCoverage.Supported finish displayRoot := by
  refine ⟨packet,List.mem_singleton_self _,rfl,GeneralNominalRefinements.installed _ _ _ _ _,?_⟩
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation,GeneralDictionaryNestedRefinement.NominalOnlyMany,
    GeneralDictionaryNestedRefinement.NominalOnly]

noncomputable def scalar_shape : GeneralDictionaryScalarIntervalInspection.Shape finish.current.context displayChild intDisplay where
  role := rfl
  entries := [(((1 : Fin 2),(1 : Fin 2)),.int)]
  observed := by intro e h; have eq := List.mem_singleton.mp h; subst e; exact ⟨rfl,rfl⟩
  inputs := rfl
  query := GeneralDictionaryUnrecordedAliasLeafExample.shape.query
  located := rfl
  defined := by intro output member; cases member

theorem child_structural : GeneralDictionaryMixedHistoricalCoverage.Structural registry displayRoot finish displayChild := by
  refine Or.inr ⟨intDisplay,by simp,int_display_checked,
    GeneralDictionaryRecordedCoverageLimit.leaf_generated,scalar_shape,?_⟩
  intro request member
  have empty : GeneralNominalMaterialization.requests finish.current.context.state registry displayChild intDisplay int_display_checked
    (GeneralNominalRecursiveInspection.bindings finish.current.context.state
      (GeneralNominalRecursiveCandidates.report finish.current.context intDisplay
        (GeneralDictionaryScalarIntervalInspection.intervals scalar_shape.entries))) = [] := by
      rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro clause member; cases member)]
      rfl
  rw [empty] at member
  cases member

private theorem two_node_path {v : B4Target.Vocabulary} {b : B4Target.SourceBoundary v}
    {r : v.Registry} {s : v.State} {origin leaf focus : v.Demand} {parentKey leafKey : Nat}
    (path : GeneralDictionarySelectionPolicy.SelectedPath b r s origin focus)
    (parentSelected : B4TargetV3.Local b r s origin (.selected parentKey [leaf]))
    (leafSelected : B4TargetV3.Local b r s leaf (.selected leafKey [])) :
    focus = origin ∨ focus = leaf := by
  induction path with
  | root => exact Or.inl rfl
  | @child parent key children child path selected member ih =>
    rcases ih with rfl | rfl
    · have same := B4TargetV3.local_functional parentSelected selected
      cases same
      exact Or.inr (List.mem_singleton.mp member)
    · have same := B4TargetV3.local_functional leafSelected selected
      cases same
      cases member

theorem path_cases (focus : Occurrence roles)
    (path : GeneralDictionarySelectionPolicy.SelectedPath
      (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry finish displayRoot focus) :
    focus = displayRoot ∨ focus = displayChild :=
  two_node_path path
    ((GeneralNominalValueBoundary.local_correspondence registry finish displayRoot _).mpr root_selected)
    ((GeneralNominalValueBoundary.local_correspondence registry finish displayChild _).mpr
      GeneralDictionaryValueRecordedCoverageLimit.leaf_selected)

theorem covered : GeneralDictionaryMixedHistoricalCoverage.Covered registry displayRoot finish := by
  intro focus path key children selected
  rcases path_cases focus path with rfl | rfl
  · exact Or.inl root_supported
  · exact child_structural

theorem classified : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
    registry finish displayRoot (.selected (.node 1 [.node 3 []])) := by
  have parent := (GeneralNominalValueBoundary.local_correspondence registry finish displayRoot _).mpr root_selected
  have leaf := (GeneralNominalValueBoundary.local_correspondence registry finish displayChild _).mpr
    GeneralDictionaryValueRecordedCoverageLimit.leaf_selected
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases leaf with
    | selected leafSafe leafUnique => exact .cons (.selected leafSafe leafUnique .nil) .nil

theorem resolves : CommonRoleOutermostResolver.Resolves
    (B4TargetV3.Local (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry finish)
    displayRoot (.selected 1 [.selected 3 []]) := by
  simpa only [B4TargetV3.render,B4TargetV3.renders] using
    B4TargetV3.render_resolves (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry finish (.node 1 [.node 3 []]) displayRoot classified

theorem completed : B4TargetV3.Completed (.selected 1 [.selected 3 []])
    (.selected (.node 1 [.node 3 []])) := .selected (.cons (.selected .nil) .nil)

theorem every_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context assignment displayRoot
      (.node 1 [.node 3 []]) :=
  GeneralDictionaryMixedHistoricalCoverage.completed_tree_evidence registry displayRoot finish
    fragment reachable covered assignment valid _ resolves _ completed

theorem actual_mixed_tree :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalValueSteps.Stable registry finish displayRoot ∧
    Models finish.current model ∧
    GeneralDictionaryMixedHistoricalCoverage.Covered registry displayRoot finish ∧
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model displayRoot (.node 1 [.node 3 []]) ∧
    ¬ ∃ packet ∈ finish.current.packets, packet.site.occurrence = displayChild :=
  ⟨reachable,stable,current_model,covered,classified,every_model model current_model,
    GeneralDictionaryRecordedCoverageLimit.no_leaf_packet⟩
end Yulang.GeneralDictionaryMixedHistoricalExample
