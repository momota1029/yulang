import Yulang.GeneralDictionaryEmissionRequestIdentity
import Yulang.GeneralDictionaryActualSchema
import Yulang.GeneralNominalReobservationSteps
import Yulang.GeneralDictionaryVariableRequirements

/-! Variable-only unnamed where arguments emit no lower/upper materialization
requests. Named RHS requests remain actual-mode. This is a restriction of this
proof, not a new language rejection rule; child demand intervals may change. -/
namespace Yulang.GeneralDictionaryVariableWhereRequests
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization
open GeneralDeclarationPatterns

def VariableInputs (declaration : Declaration) : Prop :=
  ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
    ∃ name, normalize pattern = .var name

theorem canonical_requests (invocation : Nat) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (old current : Capture) (same : current.outputs = old.outputs)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked current allocate).flatMap emissionRequests =
    (GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked old allocate).flatMap emissionRequests := by
  unfold GeneralCanonicalChildOrder.canonicalEmit emitAll
  simp only [List.flatMap_def,List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro clause _
  exact GeneralDictionaryEmissionRequestIdentity.emission_requests roles invocation _ clause.val _ old current same _

theorem emission_actual (invocation : Nat) (declaration : Declaration)
    (clause : Clause) (valid : clause.Signature roles) (capture : Capture)
    (allocate : Allocation roles clause)
    (variables : ∀ pattern ∈ clause.arguments, ∃ name, normalize pattern = .var name) :
    ∀ request ∈ emissionRequests (emit invocation declaration clause valid capture allocate), request.mode = .actual := by
  intro request member
  rcases List.mem_append.mp member with input | output
  · obtain ⟨entry,present,has⟩ := List.mem_flatMap.mp input
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    have hi : index.val < clause.arguments.length := by rw [valid.1]; exact index.isLt
    obtain ⟨name,h⟩ := variables clause.arguments[index.val] (List.getElem_mem _)
    change request ∈ inputRequests ⟨index.val,clause.arguments[index.val],_⟩ at has
    simp only [inputRequests,h] at has
    cases has
  · obtain ⟨entry,_,rfl⟩ := List.mem_map.mp output
    rfl

theorem canonical_actual (invocation : Nat) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) (variables : VariableInputs declaration) :
    ∀ request ∈ (GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked capture allocate).flatMap emissionRequests,
      request.mode = .actual := by
  intro request member
  obtain ⟨emission,present,has⟩ := List.mem_flatMap.mp member
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp present
  have member' : clause.val ∈ declaration.requirements :=
    (GeneralCanonicalChildOrder.canonicalRequirements_perm declaration.requirements).mem_iff.mpr clause.property
  exact emission_actual _ _ _ _ _ _ (variables clause.val member') request has

theorem requests_actual (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) (variables : VariableInputs declaration) :
    ∀ request ∈ requests state registry root declaration checked bindings, request.mode = .actual := by
  intro request member
  rcases List.mem_append.mp member with rootMember | emitted
  · exact GeneralDictionaryActualSchema.root_request_actual declaration root request rootMember
  · exact canonical_actual _ _ _ _ _ variables request emitted

theorem revision_requests {state : GeneralNominalSaturationState.State roles}
    (revision : GeneralNominalReobservationSteps.Revision state) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (old current : GeneralNominalAllocation.Bindings) :
    requests revision.snapshot registry root declaration checked current =
      requests state.context.state registry root declaration checked old := by
  unfold requests
  congr 1
  exact canonical_requests root.identity declaration checked
    (GeneralNominalAllocation.capture state.context.state registry root.identity declaration.id old)
    (GeneralNominalAllocation.capture revision.snapshot registry root.identity declaration.id current) rfl
    (GeneralNominalAllocation.allocation state.context.state registry root.identity declaration.id)
/-- Bare where clauses retain arbitrary real child demands, but contribute no
materialization schema requests. Root associated outputs are not restricted. -/
theorem bare_requests (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration) :
    requests state registry root declaration checked captures = rootRequests declaration root := by
  unfold requests
  have empty : (GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
      (GeneralNominalAllocation.allocation state registry root.identity declaration.id)).flatMap emissionRequests = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro emission member
    unfold GeneralCanonicalChildOrder.canonicalEmit emitAll at member
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
    have present : clause.val ∈ declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm declaration.requirements).mem_iff.mpr clause.property
    exact GeneralDictionaryVariableRequirements.emission_empty _ _ _ _ _ _
      (variables clause.val present).1 (variables clause.val present).2
  rw [empty,List.append_nil]

end Yulang.GeneralDictionaryVariableWhereRequests
