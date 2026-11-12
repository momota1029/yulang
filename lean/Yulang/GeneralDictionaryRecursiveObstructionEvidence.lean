import Yulang.GeneralDictionaryRecursiveObstruction
import Yulang.GeneralDictionaryRecursiveEvidence

/-!
# The unchanged recursive boundary cannot provide all-original-model evidence

The witness is the checked safe unique terminal candidate from the companion
fixture. The Evidence predicate is the concrete source certificate, and its
failure is forced by the declared associated-output equation, not by an invented
predicate. Step, Stable, and Generated are left arbitrary and unchanged.
-/
namespace Yulang.GeneralDictionaryRecursiveObstruction

open GeneralDeclarations
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates
open GeneralDictionaryRecursiveEvidence

/-- For this source declaration the exact missing refinement is one associated
output equality. Head captures and projections already follow from the original
state; no selection or stability property is silently added to that state. -/
theorem branch_iff_output (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration declaration_checked [(0,0)] model ↔
      GeneralNominalState.Models context.state model ∧
      CommonNominalFullCarrier.Equivalent (model 1).1 (.base .int) := by
  constructor
  · intro branch
    have original := (branch_interval_sound registry context root declaration declaration_checked
      [(0,0)] model branch).1
    have materialized := branch.2.2
    rw [schema_calculated] at materialized
    exact ⟨original,(materialized.1 (.source 1,.scalar .int) (by simp)).2 _ (.source 1)⟩
  · rintro ⟨original,equal⟩
    have head := GeneralNominalUnaryCaptureFacts.private_models context registry root declaration 0
      GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl query_exact model original
    refine ⟨head.1,head.2,?_⟩
    rw [schema_calculated]
    refine ⟨?_,?_,?_,?_⟩
    · intro test member
      have same := List.mem_singleton.mp member
      subst test
      refine ⟨⟨_,.source 1⟩,?_⟩
      intro actual observed
      cases observed
      exact equal
    · intro entry member; cases member
    · intro first member; cases member
    · intro entry member; cases member

/-- Every source instance of this visible declaration must use the computed
bounds and hence satisfy its actual scalar output test. -/
theorem instance_output_sound (model : GeneralNominalCommonBridge.Assignment) (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles))
    (instanceRule : Instance registry context model root key children) :
    CommonNominalFullCarrier.Equivalent (model 1).1 (.base .int) := by
  obtain ⟨candidate,visible,checked,_,_,bounds,located,_,_,_,_,branch⟩ := instanceRule
  have same := List.mem_singleton.mp visible
  subst candidate
  have found : arguments context root = some [(0,0)] := by decide +kernel
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  have materialized := branch.2.2
  rw [schema_calculated] at materialized
  exact (materialized.1 (.source 1,.scalar .int) (by simp)).2 _ (.source 1)

theorem bad_not_instance (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ Instance registry context badModel root key children :=
  fun instanceRule => bad_output_equation (instance_output_sound badModel key children instanceRule)

theorem evidence_output_sound (model : GeneralNominalCommonBridge.Assignment)
    (evidence : Evidence registry context model root (.node 40 [])) :
    CommonNominalFullCarrier.Equivalent (model 1).1 (.base .int) :=
  instance_output_sound model 40 [] ((evidence_leaf_iff registry context model root 40).mp evidence)

/-- Positive repair target: the actual terminal evidence holds exactly in the
original-state models satisfying the declared output equation. -/
theorem evidence_iff_output (model : GeneralNominalCommonBridge.Assignment) :
    Evidence registry context model root (.node 40 []) ↔
      GeneralNominalState.Models context.state model ∧
      CommonNominalFullCarrier.Equivalent (model 1).1 (.base .int) := by
  constructor
  · intro evidence
    exact ⟨instance_models registry context model root 40 []
      ((evidence_leaf_iff registry context model root 40).mp evidence),
      evidence_output_sound model evidence⟩
  · intro refined
    exact evidence_node_of_branch registry registry_checked context model root 40 [] []
      survivor declaration (by simp) declaration_checked rfl [(0,0)] (by decide +kernel)
      ((branch_iff_output model).mpr refined) .nil

theorem bad_not_evidence : ¬ Evidence registry context badModel root (.node 40 []) := by
  intro evidence
  exact bad_not_instance 40 [] ((evidence_leaf_iff registry context badModel root 40).mp evidence)

theorem good_evidence : Evidence registry context GeneralNominalExamples.model root (.node 40 []) :=
  evidence_node_of_branch registry registry_checked context GeneralNominalExamples.model root 40 [] []
    survivor declaration (by simp) declaration_checked rfl [(0,0)] (by decide +kernel) good_branch .nil

/-- The independent V3 classification genuinely selects this dictionary at the
original state, for every choice of the three transition fields. -/
theorem classified (remaining : GeneralNominalLocalBoundary.Remaining
    (GeneralNominalCandidates.vocabulary roles)) :
    B4TargetV3.Classify (boundary roles remaining) registry context root (.selected (.node 40 [])) :=
  .selected safe unique .nil

/-- An all-original-models EvidenceNode is false for this concrete source
Evidence and the unchanged recursive candidate fields, regardless of how the
three transition fields are filled. This does not refute a rule after branch
facts are installed in a successor state. -/
theorem no_evidenceNode (remaining : GeneralNominalLocalBoundary.Remaining
    (GeneralNominalCandidates.vocabulary roles)) :
    ¬ B4TargetV3.EvidenceNode (boundary roles remaining) :=
  no_evidenceNode_of_output_sound { remaining with Evidence := Evidence } evidence_output_sound

/-- Both the positive branch witness and the negative original-state model are
nonvacuous; the selected key and empty child list are exactly the same. -/
theorem concrete_evidence_gap :
    Evidence registry context GeneralNominalExamples.model root (.node 40 []) ∧
    GeneralNominalState.Models context.state badModel ∧
    ¬ Evidence registry context badModel root (.node 40 []) :=
  ⟨good_evidence,bad_original_model,bad_not_evidence⟩

end Yulang.GeneralDictionaryRecursiveObstruction
