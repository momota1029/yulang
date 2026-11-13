import Yulang.GeneralNominalMaterialization

/-! Input capture changes do not change emitted materialization requests when
output captures and allocation are fixed. Child demand intervals may change;
no child Evidence or endpoint-equivalence conclusion follows. -/
namespace Yulang.GeneralDictionaryEmissionRequestIdentity
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization

theorem output_target (declaration : Declaration) (old current : Capture)
    (same : current.outputs = old.outputs) (allocate : Nat → Nat) (equation : Equation) :
    outputTarget declaration current allocate equation =
      outputTarget declaration old allocate equation := by
  unfold outputTarget
  rw [same]

theorem input_requests (old current : Capture) (allocated : GeneralSourceState.Interval)
    (pattern : GeneralDeclarationPatterns.Pattern) (position : Nat) :
    inputRequests ⟨position,pattern,inputInterval current allocated pattern⟩ =
      inputRequests ⟨position,pattern,inputInterval old allocated pattern⟩ := by
  cases h : GeneralDeclarationPatterns.normalize pattern <;>
    simp only [inputRequests,inputInterval,h]

theorem emission_requests (roles : Roles.RoleDecls) (invocation : Nat)
    (declaration : Declaration) (clause : Clause) (valid : clause.Signature roles)
    (old current : Capture) (same : current.outputs = old.outputs)
    (allocation : Allocation roles clause) :
    emissionRequests (emit invocation declaration clause valid current allocation) =
      emissionRequests (emit invocation declaration clause valid old allocation) := by
  unfold emissionRequests emit
  congr 1
  · rw [List.flatMap_def,List.flatMap_def,List.map_ofFn,List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext index
    exact input_requests old current (allocation.arguments index) _ index.val
  · simp only [List.map_map]
    apply List.map_congr_left
    intro equation _
    simp only [Function.comp_apply]
    rw [output_target declaration old current same]
end Yulang.GeneralDictionaryEmissionRequestIdentity
