import Yulang.GeneralDictionaryOutputMergeRootEvidence

/-! Full root dictionary evidence in EVERY model of the concrete final state.
The recorded parent packet supplies its actual historical branch constraints;
its named scalar requests force both emitted output targets to int. No fixed
witness is substituted and no equality of current and historical contexts is
assumed. This concrete theorem does not close general V5 or establish Stable. -/
namespace Yulang.GeneralDictionaryOutputMergeAllModels
open GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeRootEvidence (rootPayload)
open GeneralNominalExamples (context state displayRoot)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDictionaryRecursiveEvidence (Instance Evidence)

theorem parent_branch (m : Assignment) (valid : Models finish.current m) :
    BranchModels registry (context true) displayRoot declaration checked [(0,0)] m :=
  valid.2.1 packet (List.mem_singleton_self _)

theorem parent_instance (m : Assignment) (valid : Models finish.current m) :
    Instance registry (context true) m displayRoot 1 [child 10,child 11] := by
  have rule := GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch registry registry_checked
    (context true) m displayRoot 1 children survivor declaration (by simp)
    checked rfl [(0,0)] rfl (parent_branch m valid)
  simpa only [children_exact] using rule

theorem source_valid (m : Assignment) (valid : Models finish.current m) :
    GeneralNominalState.Models (state true) m :=
  GeneralDictionaryRecursiveEvidence.instance_models registry (context true) m displayRoot 1
    [child 10,child 11] (parent_instance m valid)

theorem output_scalar (m : Assignment) (valid : Models finish.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    CommonNominalFullCarrier.Equivalent (m (outputTarget n)).1 (.base .int) := by
  have generated := (parent_branch m valid).2.2
  rw [schema] at generated
  have member : (Origin.source (outputTarget n),Test.scalar .int) ∈
      [(.source (outputTarget 10),.scalar .int),(.source (outputTarget 11),.scalar .int)] := by
    rcases which with rfl | rfl <;> simp
  exact (generated.1 _ member).2 _ (.source _)

theorem terminal_branch (m : Assignment) (valid : Models finish.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    BranchModels registry (context true) (child n) terminal terminal_checked [(1,1)] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [terminal_report]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨source_valid m valid,?_,?_⟩
      · intro first one last two _
        have a := List.mem_singleton.mp one
        have b := List.mem_singleton.mp two
        subst first; subst last
        exact CommonNominalFullCarrier.subtype_refl _
      · simp [GeneralNominalAllocation.merges,bindings,GeneralNominalAllocation.occurrences,
          Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All,PresenceNormalForm.Atom.Holds,
        CommonNominalFullCarrier.model,CommonNominalFullCarrier.subtype_refl]
  · rw [terminal_report]
    simp [ProjectionModels]
  · rw [terminal_schema]
    refine ⟨?_,by simp,by simp,by simp⟩
    intro test member
    have eq := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observation
    cases observation
    exact output_scalar m valid n which

theorem terminal_instance (m : Assignment) (valid : Models finish.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    Instance registry (context true) m (child n) 7 [] := by
  refine ⟨terminal,by simp,terminal_checked,rfl,rfl,[(1,1)],?_,?_,?_,?_,prepared.1,
    terminal_branch m valid n which⟩
  · change arguments (context true) (GeneralDictionaryJointMergeExample.root 0 0) = some [(1,1)]
    decide +kernel
  · rw [terminal_report]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have eq := List.mem_singleton.mp member; subst output
      exact ⟨GeneralDictionaryJointMergeExample.outputEquation,by simp,rfl⟩
    · rw [terminal_schema]
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    rw [GeneralDictionaryJointMergeExample.emissions_empty]
    rfl

theorem current_parent_instance (m : Assignment) (valid : Models finish.current m) :
    Instance registry current m displayRoot 1 [child 10,child 11] :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) current
    final_extension m valid.1 displayRoot 1 [child 10,child 11] (parent_instance m valid)

theorem current_terminal_instance (m : Assignment) (valid : Models finish.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    Instance registry current m (child n) 7 [] :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) current
    final_extension m valid.1 (child n) 7 [] (terminal_instance m valid n which)

theorem child_evidence (m : Assignment) (valid : Models finish.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    Evidence registry current m (child n) (.node 7 []) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry current m (child n) 7 [] []
    (current_terminal_instance m valid n which) .nil

/-- All final assignments, not merely the exhibited int-valued assignment,
validate the entire ordered recursive source dictionary. -/
theorem full_dictionary (m : Assignment) (valid : Models finish.current m) :
    Evidence registry current m displayRoot rootPayload :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry current m displayRoot 1 [child 10,child 11]
    [.node 7 [],.node 7 []] (current_parent_instance m valid)
    (.cons (child_evidence m valid 10 (Or.inl rfl)) (.cons (child_evidence m valid 11 (Or.inr rfl)) .nil))

end Yulang.GeneralDictionaryOutputMergeAllModels
