import Yulang.GeneralNominalRebaseActivationCheck243
import Yulang.GeneralNominalRebaseDefinitions241
set_option backward.isDefEq.respectTransparency false
/-! Allocator freshness produces the no-read check for never-allocated cells.
Allocated revisits still require the independent finite semantic-read check. -/
namespace Yulang.GeneralNominalRebaseActivationFresh243
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalRebaseDefinitions241 (entries slot)
open GeneralNominalRebaseActivation243
open GeneralNominalCenters (Site)
variable {roles : Roles.RoleDecls}

theorem private_key (registry : Registry) (root : Nat) (declaration : Declaration)
 (visible : declaration ∈ registry.declarations) (named : name ∈ declaration.inputNames)
 (purpose : Nat) (side : purpose = 0 ∨ purpose = 1) :
 origin root declaration.id purpose name 0 ∈ keys registry root := by
 apply List.mem_flatMap.mpr
 refine ⟨declaration,visible,?_⟩
 apply List.mem_append_left
 apply List.mem_append_left
 apply List.mem_flatMap.mpr
 refine ⟨name,named,?_⟩
 rcases side with rfl | rfl <;> simp

theorem checked_of_fresh (state : GeneralNominalState.State) (registry : Registry)
 (root : Nat) (declaration : Declaration) (bindings : Bindings)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles))
 (visible : declaration ∈ registry.declarations)
 (fresh : Fresh state registry root)
 (inactive : ∀ name ∈ declaration.inputNames, ∀ purpose, purpose = 0 ∨ purpose = 1 →
   origin root declaration.id purpose name 0 ∉ state.allocated)
 (covered : ∀ name ∈ reads state atoms sites, name ∈ GeneralNominalState.sources state) :
 Checked (entries state.seed root declaration.id bindings declaration.inputNames) state atoms sites := by
 intro entry member read
 obtain ⟨name,named,_,rfl | rfl⟩ :=
   (GeneralNominalRebaseDefinitions241.member_iff state.seed root declaration.id bindings declaration.inputNames).mp member
 · exact source_fresh state registry root fresh _ (private_key registry root declaration visible named 0 (Or.inl rfl))
     (inactive name named 0 (Or.inl rfl)) (covered _ read)
 · exact source_fresh state registry root fresh _ (private_key registry root declaration visible named 1 (Or.inr rfl))
     (inactive name named 1 (Or.inr rfl)) (covered _ read)

theorem checked_unallocated (state : GeneralNominalState.State) (registry : Registry)
 (root : Nat) (declaration : Declaration) (bindings : Bindings)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles))
 (visible : declaration ∈ registry.declarations)
 (fresh : Fresh state registry root) (empty : state.allocated = [])
 (covered : ∀ name ∈ reads state atoms sites, name ∈ GeneralNominalState.sources state) :
 Checked (entries state.seed root declaration.id bindings declaration.inputNames) state atoms sites :=
 checked_of_fresh state registry root declaration bindings atoms sites visible fresh
   (by intro _ _ _ _; rw [empty]; simp) covered
end Yulang.GeneralNominalRebaseActivationFresh243
