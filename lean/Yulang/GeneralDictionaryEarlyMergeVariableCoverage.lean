import Yulang.GeneralDictionaryEarlyMergeScalarStable
import Yulang.GeneralDictionaryVariableStableCoverage

/-! Nontrivial two-site alias regression for the general structural stable
coverage theorem. All operational, stability and coverage inputs are proved. -/
namespace Yulang.GeneralDictionaryEarlyMergeVariableCoverage
open GeneralDictionaryEarlyMergeScalarExample GeneralDictionaryEarlyMergeScalarClassification
open GeneralDictionaryEarlyMergeScalarJoint GeneralDictionaryEarlyMergeScalarEvidence
open GeneralDictionaryEarlyMergeScalarReadback GeneralDictionaryEarlyMergeScalarStable
open GeneralNominalExamples (context model displayRoot intDisplay int_display_checked)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState

theorem ordinary_trace : B4Target.Steps
    (GeneralDictionarySupportOrdinaryExecution.Step registry displayRoot) (start displayRoot) finish := by
  have installed : B4Target.Steps
      (GeneralDictionarySupportOrdinaryExecution.Step registry displayRoot) (start displayRoot) before :=
    .tail .refl ⟨displayRoot,.root,.install packet [] enabled novel packet_guard⟩
  have generated : Generated before.current displayRoot (child 10) := by
    apply Generated.child .root
    change (displayRoot,child 10) ∈ [] ++ packet.children.map (fun c => (displayRoot,c))
    simp only [List.nil_append]
    apply List.mem_map.mpr
    refine ⟨child 10,?_,rfl⟩
    change child 10 ∈ children
    rw [children_exact]; simp
  have absent : ¬ Alias before.current (child 10).identity (child 11).identity := by
    intro alias
    have equal : ∀ {first last : Nat}, Alias before.current first last → first = last := by
      intro first last given
      induction given with
      | refl => rfl
      | edge member => cases member
      | symm _ ih => exact ih.symm
      | trans _ _ one two => exact one.trans two
    exact distinct_children (equal alias)
  have guard := GeneralDictionarySupportEvidence.merge_guard_of_exact before
    (GeneralNominalSupportSteps.formed_exact
      (GeneralDictionaryEarlyMergeChoices.scheduled_formed registry displayRoot before before_scheduled))
    (site 10) (site 11) inputs_same
  exact .tail installed ⟨child 10,generated,.merge (site 10) (site 11) _
    (site_present 10 (Or.inl rfl)) (site_present 11 (Or.inr rfl)) inputs_same absent guard⟩

theorem covered : GeneralDictionaryVariableStableCoverage.Covered registry finish displayRoot := by
  intro focus reached key kids selected
  rcases generated_cases focus reached with rfl | rfl | rfl
  · exact Or.inl ⟨packet,List.mem_singleton_self _,rfl⟩
  · refine Or.inr ⟨intDisplay,by simp,int_display_checked,Or.inr (Or.inr ⟨shape 10⟩),?_⟩
    intro s related
    obtain ⟨leaf,k,cs,chosen⟩ := GeneralDictionaryEarlyMergeScalarJoint.covered 10 (Or.inl rfl) s related
    exact ⟨Or.inr leaf,k,cs,chosen⟩
  · refine Or.inr ⟨intDisplay,by simp,int_display_checked,Or.inr (Or.inr ⟨shape 11⟩),?_⟩
    intro s related
    obtain ⟨leaf,k,cs,chosen⟩ := GeneralDictionaryEarlyMergeScalarJoint.covered 11 (Or.inr rfl) s related
    exact ⟨Or.inr leaf,k,cs,chosen⟩

/-- The general finite-Classify induction is actually instantiated with a
recorded parent, two distinct merged unrecorded leaves, and a Stable endpoint. -/
theorem every_model_from_coverage (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry current assignment displayRoot payload :=
  GeneralDictionaryVariableStableCoverage.dictionary_evidence registry displayRoot (context true) source
    finish ordinary_trace stable covered assignment valid payload displayRoot .root classified

theorem actual_stable_alias_coverage :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    Models finish.current model ∧
    GeneralDictionaryVariableStableCoverage.Covered registry finish displayRoot ∧
    (child 10).identity ≠ (child 11).identity ∧
    Alias finish.current (child 10).identity (child 11).identity ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry current model displayRoot payload :=
  ⟨reachable,stable,finish_model,covered,distinct_children,children_aliased,
    every_model_from_coverage model finish_model⟩
end Yulang.GeneralDictionaryEarlyMergeVariableCoverage
