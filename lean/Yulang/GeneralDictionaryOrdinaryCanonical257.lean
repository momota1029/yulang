import Yulang.GeneralDictionaryOrdinaryFinite257
namespace Yulang.GeneralDictionaryOrdinaryCanonical257
open Core.PresenceGeneration PresenceNormalForm
open GeneralDictionaryOrdinaryFinite257 (rewriteAtom rewritten candidates le)
open GeneralDictionaryOrdinaryShape257 (crossAtom selfAtom lowerAtoms upperAtoms)
open GeneralDictionaryLooseIterationBook240 (atoms packet)

/-- All four candidate facts occur after the first actual replay. -/
theorem all_present (n : Nat) (positive : 0 < n) : candidates ⊆ rewritten n := by
 have growing : ∀ k, atoms 1 ⊆ atoms (k+1) := by
   intro k
   induction k with
   | zero => exact fun _ h => h
   | succ k ih => exact fun _ h => GeneralDictionaryReachableAggregate256.old_atoms (k+1) (ih h)
 have old : atoms 1 ⊆ atoms n := by
   have eq : n = (n-1)+1 := by omega
   rw [eq]
   exact growing (n-1)
 have atFirst : ∀ atom ∈ GeneralNominalVersionedInstallation231.atoms (packet 0), atom ∈ atoms n := by
   intro atom member
   apply old
   change atom ∈ [] ++ GeneralNominalVersionedInstallation231.atoms (packet 0)
   exact member
 have cross : crossAtom 0 ∈ atoms n := by
   apply atFirst
   rw [GeneralDictionaryOrdinaryShape257.added_exact]
   exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
 have self : selfAtom ∈ atoms n := by
   apply atFirst
   rw [GeneralDictionaryOrdinaryShape257.added_exact]
   exact List.mem_append_right _ (List.mem_cons_self ..)
 have lo : ∀ atom ∈ lowerAtoms 0, atom ∈ atoms n := by
   intro atom member
   apply atFirst
   rw [GeneralDictionaryOrdinaryShape257.added_exact]
   exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ member)))
 have hi : ∀ atom ∈ upperAtoms 0, atom ∈ atoms n := by
   intro atom member
   apply atFirst
   rw [GeneralDictionaryOrdinaryShape257.added_exact]
   exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ member)))
 intro atom member
 simp only [candidates,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl
 · exact List.mem_map.mpr ⟨crossAtom 0,cross,GeneralDictionaryOrdinaryFinite257.cross_fixed n 0 (by omega)⟩
 · exact List.mem_map.mpr ⟨selfAtom,self,GeneralDictionaryOrdinaryFinite257.self_fixed n⟩
 · let value := (lowerAtoms 0).head (by simp [lowerAtoms,GeneralNominalAllocation.equations])
   have present : value ∈ lowerAtoms 0 := List.mem_cons_self ..
   exact List.mem_map.mpr ⟨value,lo value present,GeneralDictionaryOrdinaryFinite257.lower_fixed n 0 positive value present⟩
 · let value := (upperAtoms 0).head (by simp [upperAtoms,GeneralNominalAllocation.equations])
   have present : value ∈ upperAtoms 0 := List.mem_cons_self ..
   exact List.mem_map.mpr ⟨value,hi value present,GeneralDictionaryOrdinaryFinite257.upper_fixed n 0 positive value present⟩

/-- This actual-family canonical representation is empty initially and exactly
four facts afterward. It is not a newly defined source Step. -/
def compact (n : Nat) : List (Atom Nat) := if n = 0 then [] else candidates

theorem membership (n : Nat) (atom : Atom Nat) : atom ∈ compact n ↔ atom ∈ rewritten n := by
 by_cases zero : n = 0
 · subst n; exact Iff.rfl
 · simp only [compact,zero,ite_false]
   exact ⟨fun member => all_present n (by omega) member,
     fun member => GeneralDictionaryOrdinaryFinite257.rewritten_finite n member⟩

theorem exact (n : Nat) (assignment : GeneralNominalCommonBridge.Assignment) :
 All CommonNominalFullCarrier.model assignment (compact n) ↔
 All CommonNominalFullCarrier.model assignment (rewritten n) := by
 constructor
 · intro valid atom member; exact valid atom ((membership n atom).mpr member)
 · intro valid atom member; exact valid atom ((membership n atom).mp member)

theorem length_bound (n : Nat) : (compact n).length ≤ 4 := by
 unfold compact
 split <;> decide

theorem stable (n : Nat) : compact (n+1) = candidates := by simp [compact]
end Yulang.GeneralDictionaryOrdinaryCanonical257
