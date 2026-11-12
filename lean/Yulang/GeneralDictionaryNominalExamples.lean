import Yulang.GeneralDictionaryNominalEquations
import Yulang.GeneralDictionaryHeadlessFixture

/-!
# A joint dictionary model containing an actual nominal constructor

All source identities share a genuine nominal value rather than the existing
Common Int fixture. This demonstrates consistency of all recorded equations;
it does not establish head readiness or select a declaration.
-/
namespace Yulang.GeneralDictionaryNominalExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryNominalEquations (Holds)
open GeneralNominalCommonBridge (Models)
open GeneralDictionaryBatchRecording (record)

abbrev nominalValue : CommonNominalFullCarrier.Ty :=
  CommonNominalFullCarrier.nominal 73 []

abbrev nominalAssignment : GeneralNominalCommonBridge.Assignment :=
  fun _ => (nominalValue, Common.rowEmpty)

theorem base_model : Models state nominalAssignment := by
  constructor
  · intro atom member; cases member
  · constructor
    · intro slot term recorded; cases recorded
    · intro pair member; cases member

theorem root_holds : Holds rootLocated.equations nominalAssignment := by
  constructor
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩

theorem child_holds : Holds childLocated.equations nominalAssignment := by
  constructor
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩

/-- Both nodes and repeated output occurrences share one actual nominal model. -/
theorem joint_model : Models (record [rootItem, childItem]) nominalAssignment := by
  apply (GeneralDictionaryNominalEquations.batch_models _ _).mpr
  refine ⟨base_model, ?_⟩
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact root_holds
  · exact child_holds

theorem tree_joint_model : Models (record tree.items) nominalAssignment := joint_model

/-- The exhibited constructor differs from the previous fixture's embedded Int. -/
theorem nominal_not_embedded_int :
    nominalValue ≠ CommonNominalFullModelMap.value (.base .int) := by
  intro same
  have observed := congrArg (CommonNominalFullCarrier.observeTy 0) same
  cases observed

end Yulang.GeneralDictionaryNominalExamples
