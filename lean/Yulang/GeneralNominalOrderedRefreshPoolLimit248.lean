import Yulang.GeneralNominalOrderedInitial248

/-! A propagated owner's reserved slots belong to the full source pool.
Consequently that entire pool cannot satisfy the sufficient protected-pool
condition for a later non-singleton merge. This does not contradict allocator
Fresh, imply a source-language rejection, or establish source reachability. -/
namespace Yulang.GeneralNominalOrderedRefreshPoolLimit248
open GeneralDeclarations GeneralNominalAllocation

theorem slot_in_propagated_sources (state : GeneralNominalState.State)
 (registry : Registry) (root : Nat) (declaration : Declaration)
 (declared : declaration ∈ registry.declarations) (oldBindings freshBindings : Bindings)
 (name : Nat) (named : name ∈ declaration.inputNames)
 (purpose : Nat) (side : purpose = 0 ∨ purpose = 1) :
 GeneralNominalRebaseDefinitions241.slot
   (propagate state registry root declaration oldBindings).seed root declaration.id purpose name freshBindings ∈
 GeneralNominalState.sources (propagate state registry root declaration oldBindings) := by
 have key := GeneralNominalOrderedInitial248.input_key registry root declaration declared name named purpose side
 have reserved : source state registry root (origin root declaration.id purpose name 0) ∈
     GeneralNominalAllocation.reserved state registry root :=
   List.mem_map.mpr ⟨_,key,rfl⟩
 unfold GeneralNominalState.sources
 apply List.mem_append_left
 apply List.mem_append_right
 change GeneralNominalRebaseDefinitions241.slot state.seed root declaration.id purpose name freshBindings ∈
   state.reserved ++ GeneralNominalAllocation.reserved state registry root
 exact List.mem_append_right _ reserved

theorem not_full_pool_fresh (state : GeneralNominalState.State)
 (registry : Registry) (root : Nat) (declaration : Declaration)
 (declared : declaration ∈ registry.declarations) (oldBindings freshBindings : Bindings)
 (name : Nat) (named : name ∈ declaration.inputNames)
 (many : (occurrences freshBindings name).length ≠ 1) :
 ¬ GeneralNominalRebaseDefinitions241.Fresh
   (propagate state registry root declaration oldBindings).seed root declaration.id freshBindings declaration.inputNames
   (GeneralNominalState.sources (propagate state registry root declaration oldBindings)) := by
 intro protectedPool
 exact (protectedPool name named many).1
   (slot_in_propagated_sources state registry root declaration declared oldBindings freshBindings name named 0 (Or.inl rfl))
end Yulang.GeneralNominalOrderedRefreshPoolLimit248
