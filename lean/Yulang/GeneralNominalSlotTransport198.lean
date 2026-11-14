import Yulang.GeneralNominalSlotFacts198
import Yulang.GeneralNominalSyntaxRefresh197
import Yulang.GeneralNominalFinishedObservation197

/-! Nominal-only Instance transport through arbitrary source-preserving slot
refinement. All inspection and allocation equalities are derived, not assumed. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalSlotTransport198
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRefinements (Refines)
open GeneralNominalSlotObservation198 (bounds)
open GeneralNominalSlotReport198 (report)
open GeneralNominalSlotFacts198
open GeneralNominalRecursiveInspection (Finished)
variable {old next : GeneralNominalCandidates.Context}
variable {roles : Roles.RoleDecls} {registry : Registry}

theorem allocation_capture (refinement : Refines old.state next.state)
    (bindings : GeneralNominalAllocation.Bindings) (root key : Nat) :
    GeneralNominalAllocation.capture next.state registry root key bindings =
      GeneralNominalAllocation.capture old.state registry root key bindings := by
  simp only [GeneralNominalAllocation.capture,GeneralNominalAllocation.source,refinement.seed]

theorem allocation_equal (refinement : Refines old.state next.state) (root key : Nat) :
    @GeneralNominalAllocation.allocation roles next.state registry root key =
      GeneralNominalAllocation.allocation old.state registry root key := by
  funext clause
  simp only [GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,refinement.seed]

theorem merges_equal (refinement : Refines old.state next.state)
    (bindings : GeneralNominalAllocation.Bindings) (root : Nat) (declaration : Declaration) :
    GeneralNominalAllocation.merges next.state registry root declaration bindings =
      GeneralNominalAllocation.merges old.state registry root declaration bindings := by
  unfold GeneralNominalAllocation.merges
  rw [allocation_capture refinement]

theorem allocation_frame (refinement : Refines old.state next.state)
    (bindings : GeneralNominalAllocation.Bindings) (root : Nat) :
    @GeneralNominalAllocation.frame roles next.state registry root bindings =
      GeneralNominalAllocation.frame old.state registry root bindings := by
  simp only [GeneralNominalAllocation.frame,allocation_capture refinement,
    allocation_equal refinement,GeneralNominalAllocation.source,refinement.seed]

theorem generated_eq (refinement : Refines old.state next.state)
    (interpretation : next.interpretation = old.interpretation)
    (observed : GeneralNominalRefinementTrace197.ObservedMany old.state
      (GeneralNominalInspection.queries old.state old.interpretation declaration) pairs)
    (root : Occurrence roles) (checked : DeclarationChecked registry.constructors roles declaration) :
    GeneralNominalRecursiveCandidates.generated registry next root declaration checked
      (pairs.map (bounds refinement.base.embed)) =
      GeneralNominalRecursiveCandidates.generated registry old root declaration checked pairs := by
  unfold GeneralNominalRecursiveCandidates.generated
  rw [candidate_report refinement interpretation observed,bindings_report refinement]
  simp only [GeneralNominalMaterialization.requests,GeneralNominalMaterialization.generated,
    allocation_capture refinement,allocation_equal refinement,refinement.constructors,interpretation]

theorem branch_transport (refinement : Refines old.state next.state)
    (interpretation : next.interpretation = old.interpretation)
    (observed : GeneralNominalRefinementTrace197.ObservedMany old.state
      (GeneralNominalInspection.queries old.state old.interpretation declaration) pairs)
    (root : Occurrence roles) (checked : DeclarationChecked registry.constructors roles declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models next.state model)
    (branch : GeneralNominalRecursiveCandidates.BranchModels registry old root declaration checked pairs model) :
    GeneralNominalRecursiveCandidates.BranchModels registry next root declaration checked
      (pairs.map (bounds refinement.base.embed)) model := by
  rw [GeneralDictionaryRecursiveEvidence.branch_models_iff] at branch ⊢
  rw [generated_eq refinement interpretation observed]
  rw [candidate_report refinement interpretation observed]
  rw [bindings_report refinement,selfChecks_report refinement,projection_report refinement,
    materialization_report refinement,allocation_capture refinement,merges_equal refinement]
  exact ⟨valid,branch.2⟩

/-- Only the old declaration syntax is restricted. The refinement can grow or
permute source slots, and no final report/Instance/Evidence is supplied. -/
theorem node_transport (shape : GeneralNominalSyntaxRefresh197.RegistrySyntax registry old)
    (refinement : Refines old.state next.state)
    (interpretation : next.interpretation = old.interpretation)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models next.state model)
    (source : GeneralDictionaryRecursiveEvidence.Instance registry old model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry next model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,pairs,located,finished,ready,kids,metadata,branch⟩ := source
  have observed := GeneralNominalFinishedObservation197.many_observed_of_finished
    (shape declaration visible) finished
  have same := candidate_report refinement interpretation observed
  refine ⟨declaration,visible,checked,identity,role,pairs.map (bounds refinement.base.embed),
    GeneralDictionaryRefinedLocations.arguments old next refinement root pairs located,?_,?_,?_,
    GeneralDictionaryRefinedLocations.metadata old next refinement interpretation registry metadata,?_⟩
  · rw [same]
    exact (finished_report refinement.base.embed _).mpr finished
  · unfold GeneralNominalRecursiveCandidates.RequestReady at ready ⊢
    rw [generated_eq refinement interpretation observed]
    exact ready
  · rw [same,bindings_report refinement]
    unfold GeneralNominalAllocation.children
    rw [allocation_frame refinement]
    exact kids
  · exact branch_transport refinement interpretation observed root checked model valid branch

theorem tree_transport (shape : GeneralNominalSyntaxRefresh197.RegistrySyntax registry old)
    (refinement : Refines old.state next.state)
    (interpretation : next.interpretation = old.interpretation)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models next.state model)
    (source : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry old model) tree) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry next model) tree := by
  induction source with
  | node rule _ ih => exact .node (node_transport shape refinement interpretation model valid rule) ih

theorem evidence_transport (shape : GeneralNominalSyntaxRefresh197.RegistrySyntax registry old)
    (refinement : Refines old.state next.state)
    (interpretation : next.interpretation = old.interpretation)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models next.state model)
    (source : GeneralDictionaryRecursiveEvidence.Evidence registry old model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry next model root payload := by
  obtain ⟨tree,readback,evidence⟩ := source
  exact ⟨tree,readback,tree_transport shape refinement interpretation model valid evidence⟩
end Yulang.GeneralNominalSlotTransport198
