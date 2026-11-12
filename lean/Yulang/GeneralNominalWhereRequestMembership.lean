import Yulang.GeneralNominalWhereAssociatedFacts

/-! Every actual clause output is retained by canonical request generation. -/
namespace Yulang.GeneralNominalWhereRequestMembership
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization

theorem canonical_emission_member (invocation : Nat) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (capture : Capture) (allocate : (clause : Clause) → Allocation roles clause)
    (clause : Clause) (member : clause ∈ declaration.requirements) :
    emit invocation declaration clause (checked.signature.2.2.2 clause member) capture (allocate clause) ∈
      GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked capture allocate := by
  apply (GeneralCanonicalChildOrder.canonicalEmit_perm invocation declaration checked capture allocate).mem_iff.mp
  apply List.mem_map.mpr
  exact ⟨⟨clause,member⟩,by simp,rfl⟩

theorem child_request_member (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (clause : Clause) (member : clause ∈ declaration.requirements)
    (equation : Equation) (present : equation ∈ clause.outputs) :
    (⟨equation.rhs,outputTarget declaration
      (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
      (GeneralNominalAllocation.allocation (roles := roles) state registry root.identity declaration.id clause).outputs equation,
      .actual⟩ : Request) ∈ requests state registry root declaration checked captures := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨_,canonical_emission_member root.identity declaration checked _ _ clause member,?_⟩
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨⟨equation.id,equation.name,equation.rhs,outputTarget declaration
    (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
    (GeneralNominalAllocation.allocation (roles := roles) state registry root.identity declaration.id clause).outputs equation⟩,?_,rfl⟩
  exact List.mem_map.mpr ⟨equation,present,rfl⟩
end Yulang.GeneralNominalWhereRequestMembership
