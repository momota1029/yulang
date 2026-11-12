import Yulang.GeneralDictionaryVariableRequirements

/-! Actual canonical allocation preserves every source where requirement.
This counts demands, not successful dictionaries or generated journal edges. -/
namespace Yulang.GeneralDictionaryEmittedChildCount
open GeneralDeclarations GeneralSourceDictionaries

theorem children_length (state : GeneralNominalState.State) (registry : Registry)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings) :
    (GeneralNominalAllocation.children state registry root declaration checked captures).length =
      declaration.requirements.length := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  rw [List.length_map]
  have order := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity declaration checked
    ((GeneralNominalAllocation.frame (roles := roles) state registry root.identity captures).capture declaration.id)
    ((GeneralNominalAllocation.frame (roles := roles) state registry root.identity captures).allocation declaration.id)
  rw [← order.length_eq]
  exact GeneralDeclarationDemands.emitAll_length ..

theorem children_empty_iff (state : GeneralNominalState.State) (registry : Registry)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children state registry root declaration checked captures = [] ↔
      declaration.requirements = [] := by
  rw [← List.length_eq_zero_iff,children_length, List.length_eq_zero_iff]

/-- Even when variable-only requirements have no materialization equations,
nonterminal source declarations still emit nonempty actual child lists. -/
theorem empty_schema_nonempty_children (context : GeneralNominalRecursiveCandidates.Context)
    (registry : Registry) (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (outputs : root.demand.outputs = [])
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (nonterminal : declaration.requirements ≠ []) :
    GeneralNominalRecursiveCandidates.generated registry context root declaration checked bounds = {} ∧
    GeneralNominalAllocation.children context.state registry root declaration checked
      (GeneralNominalRecursiveInspection.bindings context.state
        (GeneralNominalRecursiveCandidates.report context declaration bounds)) ≠ [] := by
  refine ⟨GeneralDictionaryVariableRequirements.generated_empty context registry root declaration checked bounds outputs variables,?_⟩
  intro erased
  exact nonterminal ((children_empty_iff ..).mp erased)
end Yulang.GeneralDictionaryEmittedChildCount
