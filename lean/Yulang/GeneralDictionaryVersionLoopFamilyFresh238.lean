import Yulang.GeneralDictionaryVersionLoopFamilyPacket238
set_option backward.isDefEq.respectTransparency false
/-! Exact finite reservation history for the proposed indexed family.
The next upper is outside every earlier reservation and current base source.
This is not yet a full historical-journal support theorem: ordinary atoms,
recorded packet/effect support and actual reachable history remain separate. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyFresh238
open GeneralDictionaryVersionLoopNames238
open GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopSource237 (registry root)

def keys (n : Nat) := GeneralNominalVersionedAllocation231.keys registry root.identity (repeated (lower n))
def allocated (n : Nat) := (List.range n).flatMap keys
def reserved (n : Nat) := (allocated n).map (GeneralNominalIdentities.source 3)

theorem keys_sources (n) : (keys n).map (GeneralNominalIdentities.source 3) =
 [lower (n+1),upper n,lower (n+1),upper n] := rfl

theorem reserved_member {n name} (member : name ∈ reserved n) :
 ∃ index < n, name = lower (index+1) ∨ name = upper index := by
 obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
 obtain ⟨index,before,present⟩ := List.mem_flatMap.mp present
 have inKeys : GeneralNominalIdentities.source 3 key ∈ (keys index).map (GeneralNominalIdentities.source 3) :=
   List.mem_map.mpr ⟨key,present,rfl⟩
 rw [keys_sources] at inKeys
 simp only [List.mem_cons,List.not_mem_nil,or_false] at inKeys
 refine ⟨index,List.mem_range.mp before,?_⟩
 rcases inKeys with a | a | a | a
 · exact Or.inl a
 · exact Or.inr a
 · exact Or.inl a
 · exact Or.inr a

theorem next_upper_not_reserved (n) : upper n ∉ reserved n := by
 intro member
 obtain ⟨index,before,lowerEq | upperEq⟩ := reserved_member member
 · exact separate index n lowerEq.symm
 · have same := upper_injective upperEq
   omega

theorem next_lower_not_reserved (n) : lower (n+1) ∉ reserved n := by
 intro member
 obtain ⟨index,before,lowerEq | upperEq⟩ := reserved_member member
 · have same := injective lowerEq
   omega
 · exact separate n index upperEq

theorem next_upper_not_base (n) (slot : Fin (n+4)) : upper n ≠ source n slot := by
 intro equal
 by_cases small : slot.val < 4
 · rw [source_small slot small] at equal
   have large := upper_above n
   omega
 · rw [source_large slot (by omega)] at equal
   have arith : slot.val-3 = (slot.val-4)+1 := by omega
   rw [arith] at equal
   exact separate (slot.val-4) n equal.symm

theorem next_lower_not_base (n) (slot : Fin (n+4)) : lower (n+1) ≠ source n slot := by
 intro equal
 by_cases small : slot.val < 4
 · rw [source_small slot small] at equal
   have large := lower_above n
   omega
 · rw [source_large slot (by omega)] at equal
   have same := injective equal
   have inside := slot.isLt
   omega
end Yulang.GeneralDictionaryVersionLoopFamilyFresh238
