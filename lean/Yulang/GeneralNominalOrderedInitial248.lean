import Yulang.GeneralNominalOrderedMerge248
/-! A concrete first-install adapter for the existing stable allocation rules.
Fresh plus new lo/hi keys supplies protected support; the executable prepared
solution preserves the actual old state and cross constraints and satisfies
its actual propagate operation. This is not a reused-key refresh theorem. -/
namespace Yulang.GeneralNominalOrderedInitial248
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm

theorem input_key (registry : Registry) (root : Nat) (declaration : Declaration)
 (declared : declaration ∈ registry.declarations) (name : Nat) (named : name ∈ declaration.inputNames)
 (purpose : Nat) (side : purpose = 0 ∨ purpose = 1) :
 origin root declaration.id purpose name 0 ∈ keys registry root := by
 apply List.mem_flatMap.mpr
 refine ⟨declaration,declared,?_⟩
 apply List.mem_append_left
 apply List.mem_append_left
 exact List.mem_flatMap.mpr ⟨name,named,by rcases side with rfl | rfl <;> simp⟩

theorem protected_of_new_keys (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (declared : declaration ∈ registry.declarations) (bindings : Bindings)
 (fresh : Fresh state registry root)
 (newKeys : ∀ name ∈ declaration.inputNames, ∀ purpose, purpose = 0 ∨ purpose = 1 →
   origin root declaration.id purpose name 0 ∉ state.allocated) :
 GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id bindings declaration.inputNames (GeneralNominalState.sources state) := by
 intro name named _
 constructor
 · exact source_fresh state registry root fresh (origin root declaration.id 0 name 0)
     (input_key registry root declaration declared name named 0 (Or.inl rfl))
     (newKeys name named 0 (Or.inl rfl))
 · exact source_fresh state registry root fresh (origin root declaration.id 1 name 0)
     (input_key registry root declaration declared name named 1 (Or.inr rfl))
     (newKeys name named 1 (Or.inr rfl))

theorem first_propagation_model (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (declared : declaration ∈ registry.declarations) (bindings : Bindings)
 (fresh : Fresh state registry root)
 (newKeys : ∀ name ∈ declaration.inputNames, ∀ purpose, purpose = 0 ∨ purpose = 1 →
   origin root declaration.id purpose name 0 ∉ state.allocated)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings (GeneralNominalState.sources state))
 (assignment : Assignment) (valid : GeneralNominalState.Models state assignment)
 (cross : Compatible bindings assignment) :
 ∃ extended, GeneralNominalState.Models (propagate state registry root declaration bindings) extended ∧
   (∀ name ∈ GeneralNominalState.sources state, extended name = assignment name) ∧
   (∀ name, (extended name).2 = (assignment name).2) := by
 obtain ⟨extended,merges,kept,rows⟩ := GeneralNominalOrderedMerge248.actual_merge_extension state registry root declaration bindings
   (GeneralNominalState.sources state) (protected_of_new_keys state registry root declaration declared bindings fresh newKeys) linked assignment
 refine ⟨extended,?_,kept,rows⟩
 apply (propagate_models state registry root declaration bindings extended).mpr
 refine ⟨GeneralNominalCenteredModelExtension.source_models_same state (fun name member => (kept name member).symm) valid,?_,merges⟩
 intro first one last two same
 change CommonNominalFullCarrier.Subtype (extended first.2.1).1 (extended last.2.2).1
 rw [kept first.2.1 (linked first one).1,kept last.2.2 (linked last two).2]
 exact cross first one last two same
end Yulang.GeneralNominalOrderedInitial248
