import Yulang.GeneralDictionaryFiniteJournal257
namespace Yulang.GeneralDictionaryFamilyRecognition258
open GeneralDictionaryLooseFamilyNames240 (lower upper)

theorem index_lower (n : Nat) : n < lower n := by
 induction n with
 | zero => decide
 | succ n ih => have grown := GeneralDictionaryLooseFamilyNames240.increases n; omega

theorem index_upper (n : Nat) : n < upper n := by
 have bound := (GeneralNominalVersionedDependency236.endpoints_below_slot 4 0 0 1 0
   (GeneralDictionaryLooseFamilyNames240.repeated (lower n))
   (by exact List.mem_cons_self : (lower n,4) ∈ GeneralNominalAllocation.occurrences
     (GeneralDictionaryLooseFamilyNames240.repeated (lower n)) 0)).1
 have below := index_lower n
 exact Nat.lt_trans below bound

def isLower (name : Nat) : Bool := if name ≤ 4 then false else (List.range (name+1)).any fun index => lower (index+1) == name
def isUpper (name : Nat) : Bool := if name ≤ 4 then false else (List.range (name+1)).any fun index => upper index == name

theorem lower_iff (name : Nat) : isLower name = true ↔ ∃ index, lower (index+1) = name := by
 by_cases small : name ≤ 4
 · simp only [isLower,small,ite_true,Bool.false_eq_true,false_iff]
   rintro ⟨index,same⟩
   have above := GeneralDictionaryLooseFamilyNames240.lower_above index
   omega
 simp only [isLower,small,ite_false,List.any_eq_true,List.mem_range,beq_iff_eq]
 constructor
 · rintro ⟨index,_,same⟩; exact ⟨index,same⟩
 · rintro ⟨index,rfl⟩
   exact ⟨index,by have bound := index_lower (index+1); omega,rfl⟩

theorem upper_iff (name : Nat) : isUpper name = true ↔ ∃ index, upper index = name := by
 by_cases small : name ≤ 4
 · simp only [isUpper,small,ite_true,Bool.false_eq_true,false_iff]
   rintro ⟨index,same⟩
   have above := GeneralDictionaryLooseFamilyNames240.upper_above index
   omega
 simp only [isUpper,small,ite_false,List.any_eq_true,List.mem_range,beq_iff_eq]
 constructor
 · rintro ⟨index,_,same⟩; exact ⟨index,same⟩
 · rintro ⟨index,rfl⟩
   exact ⟨index,by have bound := index_upper index; omega,rfl⟩

theorem disjoint (name : Nat) : ¬ (isLower name = true ∧ isUpper name = true) := by
 rintro ⟨lo,hi⟩
 obtain ⟨a,sameA⟩ := (lower_iff name).mp lo
 obtain ⟨b,sameB⟩ := (upper_iff name).mp hi
 exact GeneralDictionaryLooseFamilyNames240.separate a b (sameA.trans sameB.symm)

theorem small (name : Nat) (bound : name ≤ 4) : isLower name = false ∧ isUpper name = false := by
 constructor
 · apply Bool.eq_false_iff.mpr
   intro positive
   obtain ⟨i,equal⟩ := (lower_iff name).mp positive
   have above := GeneralDictionaryLooseFamilyNames240.lower_above i; omega
 · apply Bool.eq_false_iff.mpr
   intro positive
   obtain ⟨i,equal⟩ := (upper_iff name).mp positive
   have above := GeneralDictionaryLooseFamilyNames240.upper_above i; omega
end Yulang.GeneralDictionaryFamilyRecognition258
