import Yulang.GeneralDictionaryPrivateBoundary258
namespace Yulang.GeneralDictionaryEarlySearch258
open GeneralDictionaryLooseFamilyNames240 (lower upper)

def search (family : Nat → Nat) (name : Nat) : Nat → Nat → Bool
 | _,0 => false
 | start,fuel+1 =>
   if name < lower start then false
   else if family start = name then true
   else search family name (start+1) fuel

theorem lower_mono (a b : Nat) (before : a ≤ b) : lower a ≤ lower b := by
 rcases Nat.eq_or_lt_of_le before with rfl | less
 · exact Nat.le_refl _
 · exact Nat.le_of_lt (GeneralDictionaryLooseFamilyNames240.strict less)

/-- Early exit is justified by the common increasing lower envelope; the
family itself need not be monotone. Fuel bounds the searched index interval. -/
theorem exact (family : Nat → Nat) (above : ∀ index, lower index < family index)
 (name start fuel : Nat) :
 search family name start fuel = true ↔
 ∃ index, start ≤ index ∧ index < start+fuel ∧ family index = name := by
 induction fuel generalizing start with
 | zero =>
   simp only [search,Bool.false_eq_true,false_iff]
   rintro ⟨index,first,last,_⟩; omega
 | succ fuel ih =>
   by_cases stop : name < lower start
   · simp only [search,stop,ite_true,Bool.false_eq_true,false_iff]
     rintro ⟨index,first,_,same⟩
     have order := lower_mono start index first
     have bound := above index
     omega
   · by_cases found : family start = name
     · simp only [search,stop,ite_false,found,ite_true,true_iff]
       exact ⟨start,by omega,by omega,found⟩
     · simp only [search,stop,ite_false,found,ih]
       constructor
       · rintro ⟨index,first,last,same⟩; exact ⟨index,by omega,by omega,same⟩
       · rintro ⟨index,first,last,same⟩
         have different : index ≠ start := by intro equal; subst index; exact found same
         exact ⟨index,by omega,by omega,same⟩

def fastLower (name : Nat) : Bool := search (fun index => lower (index+1)) name 0 (name+1)
def fastUpper (name : Nat) : Bool := search upper name 0 (name+1)

theorem lower_exact (name : Nat) : fastLower name = true ↔ ∃ index, lower (index+1) = name := by
 rw [fastLower,exact _ GeneralDictionaryLooseFamilyNames240.increases]
 constructor
 · rintro ⟨index,_,_,same⟩; exact ⟨index,same⟩
 · rintro ⟨index,rfl⟩
   exact ⟨index,Nat.zero_le _,by have bound := GeneralDictionaryFamilyRecognition258.index_lower (index+1); omega,rfl⟩

theorem upper_envelope (index : Nat) : lower index < upper index :=
 (GeneralNominalVersionedDependency236.endpoints_below_slot 4 0 0 1 0
   (GeneralDictionaryLooseFamilyNames240.repeated (lower index))
   (by exact List.mem_cons_self : (lower index,4) ∈ GeneralNominalAllocation.occurrences
     (GeneralDictionaryLooseFamilyNames240.repeated (lower index)) 0)).1

theorem upper_exact (name : Nat) : fastUpper name = true ↔ ∃ index, upper index = name := by
 rw [fastUpper,exact _ upper_envelope]
 constructor
 · rintro ⟨index,_,_,same⟩; exact ⟨index,same⟩
 · rintro ⟨index,rfl⟩
   exact ⟨index,Nat.zero_le _,by have bound := GeneralDictionaryFamilyRecognition258.index_upper index; omega,rfl⟩

theorem lower_refines (name : Nat) : fastLower name = GeneralDictionaryFamilyRecognition258.isLower name := by
 have same := (lower_exact name).trans (GeneralDictionaryFamilyRecognition258.lower_iff name).symm
 cases first : fastLower name <;> cases last : GeneralDictionaryFamilyRecognition258.isLower name <;> simp_all

theorem upper_refines (name : Nat) : fastUpper name = GeneralDictionaryFamilyRecognition258.isUpper name := by
 have same := (upper_exact name).trans (GeneralDictionaryFamilyRecognition258.upper_iff name).symm
 cases first : fastUpper name <;> cases last : GeneralDictionaryFamilyRecognition258.isUpper name <;> simp_all
end Yulang.GeneralDictionaryEarlySearch258
