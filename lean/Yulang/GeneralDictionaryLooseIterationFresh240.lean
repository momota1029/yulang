import Yulang.GeneralDictionaryLooseIterationBookSupport240
import Yulang.GeneralDictionaryLooseFamilyFresh240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationFresh240
open GeneralDictionaryLooseIterationBook240
open GeneralDictionaryLooseFamilyNames240
open GeneralDictionaryLooseFamilyBase240 (source)
open GeneralDictionaryLooseFamilyFresh240 (keys keys_sources)

theorem allocated_step (n) : allocations (n+1) = allocations n ++ keys n := by
 rw [allocated_next]
 unfold GeneralNominalVersionedInstallation231.allocated
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
 rfl

theorem old_keys (n index : Nat) (before : index < n) (key) (member : key ∈ keys index) : key ∈ allocations n := by
 induction n with
 | zero => omega
 | succ n ih =>
   rw [allocated_step]
   by_cases last : index=n
   · subst index; exact List.mem_append_right _ member
   · exact List.mem_append_left _ (ih (by omega))

def Owned (n name : Nat) : Prop := ∃ key ∈ allocations n, GeneralNominalIdentities.source 4 key = name

theorem lower_owned (n index : Nat) (before : index < n) : Owned n (lower (index+1)) := by
 have member : lower (index+1) ∈ (keys index).map (GeneralNominalIdentities.source 4) := by rw [keys_sources]; exact List.mem_cons_self
 obtain ⟨key,present,equal⟩ := List.mem_map.mp member
 exact ⟨key,old_keys n index before key present,equal⟩
theorem upper_owned (n index : Nat) (before : index < n) : Owned n (upper index) := by
 have member : upper index ∈ (keys index).map (GeneralNominalIdentities.source 4) := by rw [keys_sources]; exact List.mem_cons_of_mem _ List.mem_cons_self
 obtain ⟨key,present,equal⟩ := List.mem_map.mp member
 exact ⟨key,old_keys n index before key present,equal⟩
theorem lower_small_or_owned (n index : Nat) (before : index ≤ n) : lower index ≤ 4 ∨ Owned n (lower index) := by
 cases index with
 | zero => exact Or.inl (by decide)
 | succ index => exact Or.inr (lower_owned n index (by omega))

theorem reserved_eq (n) : reservations n = (allocations n).map (GeneralNominalIdentities.source 4) := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [reserved_next,allocated_next,List.map_append,ih]
   rfl

theorem base_owned (n) (slot : Fin (n+5)) : source n slot ≤ 4 ∨ Owned n (source n slot) := by
 by_cases small : slot.val < 5
 · rw [GeneralDictionaryLooseFamilyBase240.source_small slot small]
   exact Or.inl (by omega)
 · rw [GeneralDictionaryLooseFamilyBase240.source_large slot (by omega)]
   exact lower_small_or_owned n (slot.val-4) (by have := slot.isLt; omega)

theorem atoms_owned (n name) (member : name ∈ (atoms n).flatMap GeneralNominalState.atomSources) : name ≤ 4 ∨ Owned n name := by
 rcases GeneralDictionaryLooseIterationBookSupport240.atoms_provenance n name member with rfl | rfl | ⟨index,before,rfl | rfl | rfl⟩
 · exact Or.inl (by decide)
 · exact Or.inl (by decide)
 · exact lower_small_or_owned n index (by omega)
 · exact Or.inr (lower_owned n index before)
 · exact Or.inr (upper_owned n index before)

theorem sources_owned (n name) (member : name ∈ GeneralNominalState.sources (context n).state) : name ≤ 4 ∨ Owned n name := by
 simp only [GeneralNominalState.sources,List.mem_append] at member
 rcases member with ((types | rows) | reserved) | ordinary
 · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp types; exact base_owned n slot
 · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp rows; exact base_owned n slot
 · change name ∈ reservations n at reserved
   rw [reserved_eq] at reserved
   exact Or.inr (List.mem_map.mp reserved)
 · exact atoms_owned n name ordinary

theorem fresh (n) : GeneralNominalVersionedAllocation231.Fresh (context n).state
 GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root.identity (packet n).bindings := by
 intro key _ present
 rcases sources_owned n _ present with small | ⟨old,owned,equal⟩
 · have large := GeneralNominalIdentities.source_above_seed 4 key
   change GeneralNominalIdentities.source 4 key ≤ 4 at small
   omega
 · have same := (GeneralNominalIdentities.source_identity 4 old key).mp equal
   exact same ▸ owned
end Yulang.GeneralDictionaryLooseIterationFresh240
