import Yulang.CommonEffectNormalHandler

/-! Integration of finite partial-handler coverage metadata with the existing
resolved dispatch layer. Arbitrary resolved test functions appear only in
this semantic preservation theorem; the generator consumes finite metadata.
Payload-pattern binding/default/guard generation remains with B2. -/
namespace Yulang.CommonEffectPartialIntegration
open CommonEffectArmCoverage (Arm ofResolved ofResolved_total ofResolved_operation)
open CommonEffectRecursiveSource (SemanticSignature partialKeys)

theorem resolved_keys_exact (signatures : List SemanticSignature) (operations : Fin count → Nat)
    (arms : Fin count → MultiOperationPayloadHandlers.Arm Nat Payload)
    (resolved : ∀ i, ∃ signature, signatures[operations i]? = some signature ∧ signature.key = (arms i).key) :
    partialKeys signatures (fun i => ofResolved (operations i) (arms i)) =
      MultiOperationPayloadHandlers.removedKeys arms := by
  have keys (i : Fin count) : (signatures[operations i]?).map (·.key) = some (arms i).key := by
    obtain ⟨signature, found, same⟩ := resolved i
    simp only [found, Option.map_some, same]
  simp only [partialKeys, ofResolved_total, ofResolved_operation, keys, MultiOperationPayloadHandlers.removedKeys]
  generalize List.finRange count = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    cases total : (arms index).total <;> simp [total, ih]
end Yulang.CommonEffectPartialIntegration
