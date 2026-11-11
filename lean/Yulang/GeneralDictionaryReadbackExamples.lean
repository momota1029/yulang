import Yulang.GeneralDictionaryModelEvidence
import Yulang.GeneralDictionaryEquationExamples

/-!
# Non-vacuous multi-child evidence readback

The existing satisfiable ordinary fixture supplies every head/output equation.
Two distinct child source identities have identical key payloads. Their order
and both repeated output obligations survive readback. No role applicability or
new fragment classification is asserted by this equation-evidence test.
-/
namespace Yulang.GeneralDictionaryReadbackExamples
open GeneralSourceDictionaries GeneralDictionaryReadback GeneralDictionaryModelEvidence
open GeneralDictionaryEquationExamples

abbrev root : Occurrence roles := ⟨100, demand⟩
abbrev left : Occurrence roles := ⟨101, demand⟩
abbrev right : Occurrence roles := ⟨102, demand⟩

inductive Package : Packages roles state where
  | leaf (identity : Nat) : Package ⟨identity, demand⟩ 0 [] located
  | branch : Package root 1 [left, right] located

abbrev tree : Dictionary roles := .node root 1 [.node left 0 [], .node right 0 []]
abbrev payload : Payload := .node 1 [.node 0 [], .node 0 []]

theorem stored_leaf (identity : Nat) :
    Evidence (StoredInstance Package) (.node ⟨identity, demand⟩ 0 []) :=
  .node ⟨located, .leaf identity, recorded⟩ (by simp)

theorem stored_tree : Evidence (StoredInstance Package) tree := by
  refine .node ⟨located, .branch, recorded⟩ ?_
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact stored_leaf 101
  · exact stored_leaf 102

theorem exact_readback : Readback root payload tree := ⟨rfl, rfl⟩

theorem stored_payload : PayloadEvidence (StoredInstance Package) root payload :=
  indexed_to_payload _ tree stored_tree

/-- This simultaneously certifies a satisfying assignment and all node equations. -/
theorem nonvacuous_model : GeneralSourceState.Models state assignment ∧
    Evidence (ModelInstance Package assignment) tree :=
  ⟨models, indexed_all_models Package tree stored_tree assignment models⟩

/-- One fixed source witness is valid in every model, not selected per assignment. -/
theorem uniform_model_readback :
    ∃ witness, Readback root payload witness ∧
      ∀ model, GeneralSourceState.Models state model → Evidence (ModelInstance Package model) witness :=
  erased_uniform_witness Package root payload ⟨tree, exact_readback, stored_tree⟩

theorem source_children_retained :
    (observations tree).map (fun event => event.1.identity) = [100, 101, 102] ∧
      erase (.node left 0 []) = erase (.node right 0 []) ∧
      ¬ DictionaryEquivalent (.node left 0 []) (.node right 0 []) := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have bad := congrArg Occurrence.identity (equivalent_root same)
  cases bad

/-- Package constructor inversion, not a generic coherence axiom. -/
theorem package_children_unique (occurrence : Occurrence roles) (key : Nat)
    (first last : List (Occurrence roles)) (located₁ located₂)
    (one : Package occurrence key first located₁) (two : Package occurrence key last located₂) :
    first = last := by
  cases one <;> cases two <;> rfl

theorem unique_indexed_witness (other : Dictionary roles) (readback : Readback root payload other)
    (evidence : Evidence (StoredInstance Package) other) : other = tree :=
  indexed_unique _ (stored_children_functional Package package_children_unique) other tree
    readback.1 readback.2 evidence stored_tree

end Yulang.GeneralDictionaryReadbackExamples
