import Yulang.GeneralDictionaryTreeLeaf

/-! Variable-only where requirements reuse captured intervals and emit real
children but no materialization equations. No child classification is assumed. -/
namespace Yulang.GeneralDictionaryVariableRequirements
open GeneralDeclarations GeneralDeclarationDemands GeneralDeclarationPatterns
open GeneralNominalMaterialization

/-- A syntax-only restriction. The requirements list may be nonempty. -/
def VariableClauses (declaration : Declaration) : Prop :=
  ∀ clause ∈ declaration.requirements, clause.outputs = [] ∧
    ∀ pattern ∈ clause.arguments, ∃ name, normalize pattern = .var name

theorem emission_empty (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocate : Allocation roles clause)
    (outputs : clause.outputs = [])
    (variables : ∀ pattern ∈ clause.arguments, ∃ name, normalize pattern = .var name) :
    emissionRequests (emit invocation declaration clause valid capture allocate) = [] := by
  simp only [emissionRequests, emit, outputs, List.map_nil, List.append_nil]
  apply List.flatMap_eq_nil_iff.mpr
  intro input member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  have bound : index.val < clause.arguments.length := by rw [valid.1]; exact index.isLt
  obtain ⟨name,equal⟩ := variables clause.arguments[index.val] (List.getElem_mem (n := index.val) bound)
  simp [inputRequests,equal]

theorem requests_empty (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (outputs : root.demand.outputs = []) (variables : VariableClauses declaration) :
    requests state registry root declaration checked captures = [] := by
  simp only [requests,rootRequests,outputs,List.flatMap_nil,List.nil_append]
  apply List.flatMap_eq_nil_iff.mpr
  intro emission member
  unfold GeneralCanonicalChildOrder.canonicalEmit emitAll at member
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have present : clause.val ∈ declaration.requirements :=
    (GeneralCanonicalChildOrder.canonicalRequirements_perm declaration.requirements).mem_iff.mpr clause.property
  exact emission_empty _ _ _ _ _ _ (variables clause.val present).1 (variables clause.val present).2

theorem generated_empty (context : GeneralNominalRecursiveCandidates.Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (outputs : root.demand.outputs = []) (variables : VariableClauses declaration) :
    GeneralNominalRecursiveCandidates.generated registry context root declaration checked bounds = {} := by
  unfold GeneralNominalRecursiveCandidates.generated
  rw [requests_empty _ _ _ _ _ _ outputs variables]
  rfl
end Yulang.GeneralDictionaryVariableRequirements
