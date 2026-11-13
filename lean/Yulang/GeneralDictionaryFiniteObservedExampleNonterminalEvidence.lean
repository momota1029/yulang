import Yulang.GeneralDictionaryFiniteObservedExampleNonterminal
import Yulang.GeneralDictionaryScalarLeaf

/-! A scalar source declaration closes the actual child of the nonempty named-output parent. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence
open GeneralDictionaryFiniteObservedExampleNonterminal
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
open GeneralNominalExamples (intDisplay)
open GeneralDictionaryFiniteObservedExample (model)
open GeneralDeclarationExamples (roles displayChild)

abbrev captures := bindings source (report context declaration [(0,0)])
abbrev frame : GeneralDictionaryEmissionPlans.Frame roles := GeneralNominalAllocation.frame source registry root.identity captures
abbrev child := GeneralDictionaryEmissionPlans.occurrence frame
  (GeneralDeclarationDemands.emit root.identity declaration displayChild
    (checked.signature.2.2.2 displayChild (List.mem_singleton_self _))
    (frame.capture declaration.id) (frame.allocation declaration.id displayChild))

theorem children_exact : children = [child] := by
  have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
  simp only [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,canonical]
  rfl

theorem child_arguments : arguments context child = some [(1,1)] := by
  decide +kernel

abbrev leafShape : GeneralDictionaryScalarLeaf.ScalarLeafShape context child intDisplay where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := 1
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate]
  located := child_arguments

theorem child_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    Instance registry context assignment child intDisplay.id [] :=
  GeneralDictionaryScalarLeaf.instance_of_shape context registry child intDisplay (by simp)
    GeneralDictionaryFiniteObservedExampleNonterminal.int_display_checked leafShape metadata assignment valid

theorem child_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    Evidence registry context assignment child (.node intDisplay.id []) :=
  (evidence_leaf_iff registry context assignment child intDisplay.id).mpr (child_instance assignment valid)

abbrev payload : GeneralDictionaryReadback.Payload := .node declaration.id [.node intDisplay.id []]

theorem full_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) : Evidence registry context assignment root payload := by
  have parent := GeneralDictionaryFiniteTreeBranch.instance_of_shape context registry root declaration
    (by simp) checked shape metadata assignment valid
  apply evidence_node registry context assignment root declaration.id children _ parent
  rw [children_exact]
  exact .cons (child_evidence assignment valid) .nil

/-- Every initial source model validates the whole two-node dictionary, with its
nonempty named output request and actual child retained. Stability is not claimed. -/
theorem reachable_inhabited_full_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry context model root payload ∧ root.demand.outputs ≠ [] ∧ children.length = 1 :=
  ⟨actual_reachable,initial_models,full_evidence model source_models,named_request_present,actual_children_count⟩
end Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence
