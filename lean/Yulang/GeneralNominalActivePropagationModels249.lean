import Yulang.GeneralNominalActiveMerge249
/-! Exact public-model comparison for actual propagation. New cross inequalities
are retained on the input side, rather than silently asserted redundant. -/
namespace Yulang.GeneralNominalActivePropagationModels249
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalState GeneralNominalCommonBridge
open GeneralNominalActiveMerge249

def PublicAgrees (publicNames : List Nat) (assignment boundary : Assignment) : Prop :=
 ∀ name ∈ publicNames, assignment name = boundary name

theorem public_models_iff (state : State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (bindings : Bindings) (publicNames : List Nat)
 (protectedPool : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id bindings declaration.inputNames
   (protectedSources state bindings publicNames)) (boundary : Assignment) :
 (∃ assignment, Models state assignment ∧ Compatible bindings assignment ∧ PublicAgrees publicNames assignment boundary) ↔
 (∃ assignment, Models (propagate state registry root declaration bindings) assignment ∧ PublicAgrees publicNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,cross,agree⟩
   obtain ⟨extended,newValid,_,kept,_⟩ := propagation_model state registry root declaration bindings publicNames
     protectedPool assignment valid cross
   exact ⟨extended,newValid,fun name member => (kept name member).trans (agree name member)⟩
 · rintro ⟨assignment,valid,agree⟩
   obtain ⟨oldValid,cross,_⟩ := (propagate_models state registry root declaration bindings assignment).mp valid
   exact ⟨assignment,oldValid,cross,agree⟩

theorem bounded_public_models_iff (state : State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (bindings : Bindings) (publicNames : List Nat)
 (bounded : ∀ name ∈ protectedSources state bindings publicNames, name ≤ state.seed) (boundary : Assignment) :
 (∃ assignment, Models state assignment ∧ Compatible bindings assignment ∧ PublicAgrees publicNames assignment boundary) ↔
 (∃ assignment, Models (propagate state registry root declaration bindings) assignment ∧ PublicAgrees publicNames assignment boundary) :=
 public_models_iff state registry root declaration bindings publicNames
   (protected_of_bounded state root declaration bindings publicNames bounded) boundary
end Yulang.GeneralNominalActivePropagationModels249
