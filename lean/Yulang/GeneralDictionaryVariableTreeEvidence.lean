import Yulang.GeneralDictionaryVariableTreeExample

namespace Yulang.GeneralDictionaryVariableTreeEvidence
open GeneralDictionaryVariableTreeExample
open GeneralNominalBranchExample (state context root model state_models)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralDeclarationPatterns

abbrev captures := bindings state (report context declaration [(0,0)])
abbrev frame : GeneralDictionaryEmissionPlans.Frame roles := GeneralNominalAllocation.frame state registry root.identity captures
abbrev child := GeneralDictionaryEmissionPlans.occurrence frame
  (GeneralDeclarationDemands.emit root.identity declaration clause
    (checked.signature.2.2.2 clause (List.mem_singleton_self _))
    (frame.capture declaration.id) (frame.allocation declaration.id clause))

theorem children_exact : children = [child] := by
  have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
  simp only [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,canonical]
  rfl

theorem captures_exact : captures = [(0,1,1),(1,2,2)] := by
  have equal : captures = List.ofFn (fun i => (names i,state.base.source (bounds i).1,state.base.source (bounds i).2)) := by
    unfold captures
    rw [GeneralNominalTreeFacts.report_exact context declaration tree shape.query]
    exact GeneralNominalTreeFacts.tree_bindings state tree none
  simpa [names,bounds,List.ofFn_succ] using equal

theorem child_arguments : arguments context child = some [(1,1)] := by
  simp [arguments,GeneralNominalCandidates.arguments,
    child,GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
    frame,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,captures_exact,
    GeneralNominalAllocation.occurrences,normalize,List.ofFn_succ]
  rfl

theorem leaf_checked : DeclarationChecked constructors roles leafDeclaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp

abbrev leafShape : GeneralDictionaryTreeLeaf.TreeLeafShape context child leafDeclaration where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := 1
  arity := 0
  names := Fin.elim0
  distinct := by intro i; exact Fin.elim0 i
  inputs := rfl
  bounds := Fin.elim0
  tree := .leaf Fin.elim0 Fin.elim0 1 GeneralNominalBranchExample.left rfl rfl
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,GeneralNominalBranchExample.interpretation,
      GeneralNominalTreeFacts.Tree.query]
  located := child_arguments

theorem child_instance : Instance registry context model child leafDeclaration.id [] :=
  GeneralDictionaryTreeLeaf.instance_of_shape context registry child leafDeclaration (by simp)
    leaf_checked leafShape metadata model state_models

theorem child_evidence : Evidence registry context model child (.node leafDeclaration.id []) :=
  (evidence_leaf_iff registry context model child leafDeclaration.id).mpr child_instance

theorem full_evidence : Evidence registry context model root
    (.node declaration.id [.node leafDeclaration.id []]) := by
  apply evidence_node registry context model root declaration.id children _ actual_instance
  rw [children_exact]
  exact .cons child_evidence .nil

/-- A genuine initial-source, inhabited state has a nonterminal dictionary with
its actual emitted child evidence. No Stable or execution claim is made. -/
theorem reachable_inhabited_full_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry start.current.context model root
      (.node declaration.id [.node leafDeclaration.id []]) ∧ children ≠ [] :=
  ⟨actual_reachable,initial_models,full_evidence,inhabited_nonterminal.2.2⟩
end Yulang.GeneralDictionaryVariableTreeEvidence
