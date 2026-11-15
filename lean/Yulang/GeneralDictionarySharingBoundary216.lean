import Yulang.GeneralDictionaryCountedProjection216

/-! A helper-boundary regression, not a reachable or selected counterexample.
Tests of repeated variables are empty and cannot establish capture sharing. -/
namespace Yulang.GeneralDictionarySharingBoundary216
open GeneralNominalMaterialization GeneralNominalOriginTerms
open CommonNominalFullCarrier GeneralDictionaryInspectionHeads215
open GeneralNominalCommonBridge (Assignment)

 def witness : Assignment := fun n => (if n = 0 then .base .int else .base .bool, fun _ => False)

 def repeated : Schema := schemas [.variables [7],.variables [7]] (fun n => .source n) .actual 0

 theorem tests_empty : repeated.tests = [] := by simp [repeated,schemas,schema,Schema.append]

 theorem tests_valid : ∀ test ∈ repeated.tests, Head witness test.1 test.2 := by
  intro test member
  rw [tests_empty] at member
  cases member

 theorem origins_differ : ¬ Same witness (.source 0) (.source 1) := by
  intro same
  have equal := same.2.2 (witness 0).1 (witness 1).1 (.source 0) (.source 1)
  have impossible := tag_subtype (tagged_scalar .int) (tagged_scalar .bool) equal.1
  cases impossible

 theorem tests_not_sharing :
    (∀ test ∈ repeated.tests, Head witness test.1 test.2) ∧ ¬ Same witness (.source 0) (.source 1) :=
  ⟨tests_valid,origins_differ⟩

end Yulang.GeneralDictionarySharingBoundary216
