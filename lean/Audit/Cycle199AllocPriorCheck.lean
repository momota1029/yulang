import Yulang.GeneralDictionaryMatPriorConflict199
import Yulang.GeneralNominalCenteredHeadAllocBoundary
set_option backward.isDefEq.respectTransparency false
open Yulang
open GeneralDictionaryMatPriorConflictSource199
namespace Yulang.Cycle199AllocPriorCheck
theorem encoded_registry_eq : GeneralNominalCenteredHeadAllocEncoding.registry registry = registry := rfl
theorem not_prior_evidenceNode : ¬ B4SkeletonV5.EvidenceNode
    (B4TargetV6.prior (GeneralNominalCenteredHeadAllocBoundary.boundary roles)) := by
  intro node
  apply GeneralDictionaryMatPriorConflict199.no_evidence
  have chosen := GeneralDictionaryMatPriorConflictLocal199.unique
  rw [GeneralDictionaryMatPriorConflict199.children_empty] at chosen
  exact node registry ⟨rfl,checked⟩ start root ⟨start,initial_source,.refl⟩ model inhabited root 37 [] []
    (Or.inl rfl) GeneralDictionaryMatPriorConflict199.stable
    (by intro child member; cases member) GeneralDictionaryMatPriorConflictLocal199.safe chosen .nil

#print axioms encoded_registry_eq
#print axioms not_prior_evidenceNode
end Yulang.Cycle199AllocPriorCheck
