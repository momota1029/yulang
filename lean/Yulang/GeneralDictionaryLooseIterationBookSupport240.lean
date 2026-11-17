import Yulang.GeneralDictionaryLooseIterationAtomSupport240
import Yulang.GeneralDictionaryLooseIterationBook240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationBookSupport240
open GeneralDictionaryLooseIterationBook240
open GeneralDictionaryLooseFamilyNames240
open GeneralNominalState (atomSources)

theorem atoms_provenance (n : Nat) (name : Nat) (member : name ∈ (atoms n).flatMap atomSources) :
 name = 3 ∨ name = 4 ∨ ∃ index < n, name = lower index ∨ name = lower (index+1) ∨ name = upper index := by
 induction n with
 | zero => cases member
 | succ n ih =>
   rw [atoms_next,List.flatMap_append] at member
   rcases List.mem_append.mp member with old | added
   · rcases ih old with same | same | ⟨index,before,same⟩
     · exact Or.inl same
     · exact Or.inr (Or.inl same)
     · exact Or.inr (Or.inr ⟨index,by omega,same⟩)
   · have found := GeneralDictionaryLooseIterationAtomSupport240.atom_sources n (allocations n) (reservations n) (atoms n) added
     simp only [List.mem_cons,List.not_mem_nil,or_false] at found
     rcases found with same | same | same | same | same
     · exact Or.inl same
     · exact Or.inr (Or.inl same)
     · exact Or.inr (Or.inr ⟨n,by omega,Or.inl same⟩)
     · exact Or.inr (Or.inr ⟨n,by omega,Or.inr (Or.inl same)⟩)
     · exact Or.inr (Or.inr ⟨n,by omega,Or.inr (Or.inr same)⟩)

theorem upper_not_lower (index stage : Nat) : upper stage ≠ lower index := by
 cases index with
 | zero => have large := upper_above stage; change upper stage ≠ 2; omega
 | succ index => exact Ne.symm (separate index stage)

theorem fresh_upper (stage index : Nat) (later : stage ≤ index) :
 upper index ∉ (atoms stage).flatMap atomSources := by
 intro member
 rcases atoms_provenance stage _ member with equal | equal | ⟨old,before,equal | equal | equal⟩
 · have large := upper_above index; omega
 · have large := upper_above index; omega
 · exact upper_not_lower old index equal
 · exact upper_not_lower (old+1) index equal
 · have same := upper_injective equal
   omega
end Yulang.GeneralDictionaryLooseIterationBookSupport240
