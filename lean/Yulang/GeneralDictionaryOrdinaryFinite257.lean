import Yulang.GeneralDictionaryOrdinaryShape257
import Yulang.GeneralDictionaryFullReduced257
namespace Yulang.GeneralDictionaryOrdinaryFinite257
open Core.PresenceGeneration PresenceNormalForm
open GeneralDictionaryUpperHistory257 (history)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceDefinitionRewrite244 (atomSubst)
open GeneralPresenceIdempotentTree257 (reduce join meet)
open GeneralDictionaryOrdinaryShape257 (crossAtom selfAtom lowerAtoms upperAtoms)
open GeneralDictionaryLooseIterationBook240 (atoms)

def rewriteAtom (n : Nat) (atom : Atom Nat) : Atom Nat :=
 GeneralPresenceIdempotentTree257.atom (atomSubst (mapping (history n)) atom)

def le (a b : Nat) : Atom Nat := .tyLe (.var a) (.var b)
def candidates : List (Atom Nat) := [le 2 4,le 3 3,le 2 2,le 4 4]

theorem cross_fixed (n index : Nat) (before : index ≤ n) :
 rewriteAtom n (crossAtom index) = le 2 4 := by
 change Atom.tyLe (reduce (mapping (history n) (GeneralDictionaryLooseFamilyNames240.lower index)).ty)
   (reduce (mapping (history n) 4).ty) = _
 rw [GeneralDictionaryFullReduced257.lower_fixed n index before,
   GeneralDictionaryFullReduced257.initial_fixed n 4 (by decide)]
 rfl

theorem self_fixed (n : Nat) : rewriteAtom n selfAtom = le 3 3 := by
 change Atom.tyLe (reduce (mapping (history n) 3).ty) (reduce (mapping (history n) 3).ty) = _
 rw [GeneralDictionaryFullReduced257.initial_fixed n 3 (by decide)]
 rfl

theorem lower_fixed (n index : Nat) (before : index < n) (atom : Atom Nat)
 (member : atom ∈ lowerAtoms index) : rewriteAtom n atom = le 2 2 := by
 simp only [lowerAtoms,GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl
 all_goals
   simp only [rewriteAtom,GeneralPresenceIdempotentTree257.atom,atomSubst,TyTerm.subst,reduce]
   rw [GeneralDictionaryFullReduced257.lower_fixed n (index+1) (by omega),
     GeneralDictionaryFullReduced257.lower_fixed n index (by omega)]
   rfl

theorem upper_fixed (n index : Nat) (before : index < n) (atom : Atom Nat)
 (member : atom ∈ upperAtoms index) : rewriteAtom n atom = le 4 4 := by
 simp only [upperAtoms,GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl
 all_goals
   simp only [rewriteAtom,GeneralPresenceIdempotentTree257.atom,atomSubst,TyTerm.subst,reduce]
   rw [GeneralDictionaryFullReduced257.upper_fixed n index before,
     GeneralDictionaryFullReduced257.initial_fixed n 4 (by decide)]
   rfl

theorem finite (n : Nat) (atom : Atom Nat) (member : atom ∈ atoms n) : rewriteAtom n atom ∈ candidates := by
 obtain ⟨index,before,kind⟩ := GeneralDictionaryOrdinaryShape257.atom_cases n atom member
 rcases kind with rfl | rfl | lo | hi
 · rw [cross_fixed n index (by omega)]; exact List.mem_cons_self ..
 · rw [self_fixed]; simp [candidates]
 · rw [lower_fixed n index before atom lo]; simp [candidates]
 · rw [upper_fixed n index before atom hi]; simp [candidates]

def rewritten (n : Nat) : List (Atom Nat) := (atoms n).map (rewriteAtom n)

theorem rewritten_finite (n : Nat) : rewritten n ⊆ candidates := by
 intro atom member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact finite n original present

theorem length_rewritten (n : Nat) : (rewritten n).length = 16*n := by
 rw [rewritten,List.length_map,GeneralDictionaryOrdinaryShape257.length_atoms]
end Yulang.GeneralDictionaryOrdinaryFinite257
