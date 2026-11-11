import Yulang.GeneralDictionarySemanticUniqueness
import Yulang.GeneralDictionarySemanticOrderExamples

/-! # Concrete uniqueness of unordered equation evidence
The package constructor, rather than an assumed source oracle, determines each
key and its canonical child list. This remains an equation-evidence fixture. -/
namespace Yulang.GeneralDictionaryUniquenessExamples
open GeneralSourceDictionaries GeneralDictionaryReadback GeneralDictionaryModelEvidence
open GeneralDictionarySemanticOrder GeneralDictionarySemanticUniqueness
open GeneralDictionarySemanticOrderExamples
open GeneralDictionaryEquationExamples (roles state)

theorem package_functional : PackagesFunctional Package := by
  intro occurrence key₁ key₂ first last located₁ located₂ one two
  cases one <;> cases two <;> exact ⟨rfl, rfl⟩

theorem stored_source_unique (first last : Dictionary roles)
    (one : Evidence (StoredInstance (Unordered Package)) first)
    (two : Evidence (StoredInstance (Unordered Package)) last)
    (root : last.root = first.root) : DictionaryEquivalent first last :=
  evidence_unique _ (stored_functional Package package_functional) first one last root two

theorem model_source_unique (assignment : GeneralSourceState.Assignment) (first last : Dictionary roles)
    (one : Evidence (ModelInstance (Unordered Package) assignment) first)
    (two : Evidence (ModelInstance (Unordered Package) assignment) last)
    (root : last.root = first.root) : DictionaryEquivalent first last :=
  evidence_unique _ (model_functional Package package_functional assignment) first one last root two

theorem any_root_payload_equivalent (payload : Payload)
    (given : PayloadEvidence (StoredInstance (Unordered Package)) root payload) :
    GeneralDictionaryPayloadOrder.Equivalent payload backward :=
  payload_unique _ (stored_functional Package package_functional) root payload backward given backward_semantic

end Yulang.GeneralDictionaryUniquenessExamples
