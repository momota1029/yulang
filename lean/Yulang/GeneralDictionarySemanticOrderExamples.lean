import Yulang.GeneralDictionarySemanticOrder
import Yulang.GeneralDictionaryEquationExamples

/-!
# Canonical readback is strict; semantic sibling evidence is unordered

Distinct source children have distinct leaf keys. Swapping only payload order
cannot pass the original ordered package, but passes its source-preserving
semantic view with the corresponding source permutation. The state is satisfiable.
-/
namespace Yulang.GeneralDictionarySemanticOrderExamples
open GeneralSourceDictionaries GeneralDictionaryReadback GeneralDictionaryModelEvidence
open GeneralDictionaryPayloadOrder GeneralDictionarySemanticOrder
open GeneralDictionaryEquationExamples

abbrev root : Occurrence roles := ⟨200, demand⟩
abbrev left : Occurrence roles := ⟨201, demand⟩
abbrev right : Occurrence roles := ⟨202, demand⟩

inductive Package : Packages roles state where
  | left : Package left 2 [] located
  | right : Package right 3 [] located
  | branch : Package root 7 [left, right] located

abbrev forward : Payload := .node 7 [.node 2 [], .node 3 []]
abbrev backward : Payload := .node 7 [.node 3 [], .node 2 []]

theorem forward_stored : PayloadEvidence (StoredInstance Package) root forward :=
  .node ⟨located, .branch, recorded⟩
    (.cons (.node ⟨located, .left, recorded⟩ .nil)
      (.cons (.node ⟨located, .right, recorded⟩ .nil) .nil))

theorem forward_backward_equivalent : Equivalent forward backward :=
  .reorder 7 (.swap _ _ _)

/-- The two ordered raw key trees are genuinely different. -/
theorem forward_backward_distinct : forward ≠ backward := by
  intro same
  cases same

/-- A source-left obligation cannot acquire the source-right implementation key. -/
theorem left_wrong_key (children : List Payload) :
    ¬ PayloadEvidence (StoredInstance Package) left (.node 3 children) := by
  intro derived
  cases derived with
  | node instanceRule _ =>
      obtain ⟨_, package, _⟩ := instanceRule
      cases package

/-- The semantic adapter does not pretend the canonical ordered checker passed. -/
theorem backward_not_canonical : ¬ PayloadEvidence (StoredInstance Package) root backward := by
  intro derived
  cases derived with
  | node instanceRule children =>
      obtain ⟨_, package, _⟩ := instanceRule
      cases package
      cases children with
      | cons first _ => exact left_wrong_key [] first

theorem backward_semantic : PayloadEvidence (StoredInstance (Unordered Package)) root backward :=
  equivalent_stored_payload Package root forward backward forward_backward_equivalent forward_stored

theorem backward_all_models (assignment : GeneralSourceState.Assignment)
    (model : GeneralSourceState.Models state assignment) :
    PayloadEvidence (ModelInstance (Unordered Package) assignment) root backward :=
  equivalent_payload_all_models Package root forward backward forward_backward_equivalent
    forward_stored assignment model

theorem backward_nonvacuous : GeneralSourceState.Models state assignment ∧
    PayloadEvidence (ModelInstance (Unordered Package) assignment) root backward :=
  ⟨models, backward_all_models assignment models⟩

theorem backward_uniform_source_witness :
    ∃ tree, Readback root backward tree ∧
      ∀ model, GeneralSourceState.Models state model → Evidence (ModelInstance (Unordered Package) model) tree :=
  equivalent_uniform_witness Package root forward backward forward_backward_equivalent forward_stored

/-- Permutation admits both sibling orders while retaining their distinct IDs. -/
theorem unordered_not_ordered_functional :
    ¬ ChildrenFunctional (StoredInstance (Unordered Package)) := by
  intro functional
  have first : StoredInstance (Unordered Package) root 7 [left, right] :=
    ⟨located, ⟨[left, right], .refl _, .branch⟩, recorded⟩
  have last : StoredInstance (Unordered Package) root 7 [right, left] :=
    ⟨located, ⟨[left, right], .swap _ _ _, .branch⟩, recorded⟩
  have same := functional root 7 _ _ first last
  have head := (List.cons.inj same).1
  have ids := congrArg Occurrence.identity head
  cases ids

end Yulang.GeneralDictionarySemanticOrderExamples
