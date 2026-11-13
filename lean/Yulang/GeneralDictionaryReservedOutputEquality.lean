import Yulang.GeneralDictionaryReservedInstalledEvidence

/-! The journal's named-output equation is stronger than the raw source view.
These semantic equalities justify a real equality-feedback transition. -/
namespace Yulang.GeneralDictionaryReservedOutputEquality
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration arguments model descriptor)
open GeneralNominalSaturationState GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

/-- A nominal head and scalar tests at every position determine an arbitrary
finite repeated-scalar nominal value. Neither a source slot nor an initial
observation is required. -/
theorem nominal_repeated_scalar (assignment : GeneralNominalCommonBridge.Assignment) (source name count : Nat)
    (scalar : Inference.Base)
    (head : Test.Holds (.nominal name count) (assignment source).1)
    (children : ∀ index, index < count →
      (∃ actual, Observes assignment (.nominal (.source source) name index) actual) ∧
      ∀ actual, Observes assignment (.nominal (.source source) name index) actual → Equivalent actual (.base scalar)) :
    Equivalent (assignment source).1 (nominal name (List.replicate count (.inl (.base scalar)))) := by
  obtain ⟨args,size,equal⟩ := head
  have entries : ∀ (index : Nat) (a : Argument), args[index]? = some a → ArgumentEquivalent a (.inl (.base scalar)) := by
    intro index a found
    have bound : index < count := by
      have := (List.getElem?_eq_some_iff.mp found).1
      omega
    obtain ⟨⟨actual,seen⟩,test⟩ := children index bound
    have scalarEqual := test actual seen
    cases seen with
    | nominal parent other lookup =>
      cases parent
      have inv := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans equal.2 other.1)
      have agree := inv.2.2 index a (.inl actual) found lookup
      cases a with
      | inr => cases agree
      | inl value => exact ⟨subtype_trans agree.1 scalarEqual.1,subtype_trans scalarEqual.2 agree.2⟩
  have forward : Subtype (nominal name args) (nominal name (List.replicate count (.inl (.base scalar)))) := by
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,by simpa using size,?_⟩
    intro index a b first last
    have same : b = .inl (.base scalar) := by
      have member := List.mem_of_getElem? last
      simp only [List.mem_replicate] at member
      exact member.2
    subst b
    exact entries _ _ first
  have backward : Subtype (nominal name (List.replicate count (.inl (.base scalar)))) (nominal name args) := by
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,by simpa using size.symm,?_⟩
    intro index a b first last
    have same := ((nominal_regular_invariant_exact ..).mp forward).2.2 index b a last first
    cases a <;> cases b <;> first | exact same.symm | exact And.symm same | exact False.elim same
  exact ⟨subtype_trans equal.1 forward,subtype_trans backward equal.2⟩

theorem output_equal (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Equivalent (assignment 2).1 (nominal 0 arguments) := by
  have recorded := (GeneralNominalPacketSupport.packet_exact packet assignment).mp (valid.2.1 packet packet_recorded)
  have schema := recorded.2.2
  change GeneralNominalMaterialization.Models state declaration _ _
    (GeneralNominalMaterialization.generated state GeneralDictionaryFiniteObservedExample.interpretation
      (GeneralNominalMaterialization.requests state registry root declaration GeneralDictionaryFiniteObservedExample.checked _)) assignment at schema
  rw [actual_requests_exact] at schema
  apply nominal_repeated_scalar assignment 2 0 3 .int
  · exact (schema.1 (.source 2,.nominal 0 3) (by rw [tests_exact]; simp)).2 _ (.source 2)
  · intro index small
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    apply schema.1 (.nominal (.source 2) 0 index,.scalar .int)
    rw [tests_exact]
    rcases cases with rfl | rfl | rfl <;> simp

theorem source_equal (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Equivalent (assignment 0).1 (nominal 0 arguments) := by
  have old := ((GeneralNominalFeedbackSites.install_models start.current packet _ rfl assignment).mp valid).1.1
  have tests := (GeneralDictionaryObservedFiniteRequests.generated_valid
    GeneralDictionaryFiniteObservedExample.state GeneralDictionaryFiniteObservedExample.interpretation
    [GeneralDictionaryFiniteObservedExample.request] GeneralDictionaryFiniteObservedExample.observed assignment old).2.2
  have exactTests : (GeneralNominalMaterialization.generated GeneralDictionaryFiniteObservedExample.state
      GeneralDictionaryFiniteObservedExample.interpretation [GeneralDictionaryFiniteObservedExample.request]).tests =
      [(.source 0,.nominal 0 3),(.nominal (.source 0) 0 0,.scalar .int),
        (.nominal (.source 0) 0 1,.scalar .int),(.nominal (.source 0) 0 2,.scalar .int)] := by
    simp [GeneralNominalMaterialization.generated,GeneralDictionaryFiniteObservedExample.request,
      GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDictionaryFiniteObservedExample.interpretation,
      GeneralNominalExamples.interpretation,GeneralDictionaryFiniteObservedExample.constructors,
      GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append]
  apply nominal_repeated_scalar assignment 0 0 3 .int
  · exact (tests (.source 0,.nominal 0 3) (by rw [exactTests]; simp)).2 _ (.source 0)
  · intro index small
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    apply tests (.nominal (.source 0) 0 index,.scalar .int)
    rw [exactTests]
    rcases cases with rfl | rfl | rfl <;> simp

theorem journal_equal : GeneralNominalFeedbackK2.Equal installed.current 2 0 := by
  intro assignment valid
  have one := output_equal assignment valid
  have two := source_equal assignment valid
  exact ⟨subtype_trans one.1 two.2,subtype_trans two.1 one.2⟩

end Yulang.GeneralDictionaryReservedOutputEquality
