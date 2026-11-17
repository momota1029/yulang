import Yulang.GeneralNominalVersionedAggregateReuse236
set_option backward.isDefEq.respectTransparency false
/-! Exact equality between the kernel's versioned merge atom list and the
finite target/expression entries used by constructive assignment patches. -/
namespace Yulang.GeneralNominalVersionedAggregateEntries236
open GeneralNominalAllocation (occurrences equations)
open GeneralNominalVersionedAggregateRealization236 (entries)

theorem atoms_eq (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
 (root : Nat) (declaration : GeneralDeclarations.Declaration) (bindings) :
 GeneralNominalVersionedAllocation231.merges state registry root declaration bindings =
 (entries state.seed root declaration.id bindings declaration.inputNames).flatMap
   (fun entry => equations entry.1 entry.2) := by
 unfold GeneralNominalVersionedAllocation231.merges entries
 rw [List.flatMap_assoc]
 apply congrArg (fun f : Nat → List (PresenceNormalForm.Atom Nat) => declaration.inputNames.flatMap f)
 funext name
 cases found : occurrences bindings name with
 | nil => simp [found,GeneralNominalVersionedAllocation231.capture]
 | cons head rest =>
   cases rest with
   | nil => simp
   | cons next tail => simp [found,GeneralNominalVersionedAllocation231.capture]

theorem holds_iff (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
 (root : Nat) (declaration : GeneralDeclarations.Declaration) (bindings) (model) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model
   (GeneralNominalVersionedAllocation231.merges state registry root declaration bindings) ↔
 ∀ entry ∈ entries state.seed root declaration.id bindings declaration.inputNames,
   PresenceNormalForm.All CommonNominalFullCarrier.model model (equations entry.1 entry.2) := by
 rw [atoms_eq]
 constructor
 · intro valid entry member atom present
   exact valid atom (List.mem_flatMap.mpr ⟨entry,member,present⟩)
 · intro valid atom member
   obtain ⟨entry,present,within⟩ := List.mem_flatMap.mp member
   exact valid entry present atom within
end Yulang.GeneralNominalVersionedAggregateEntries236
