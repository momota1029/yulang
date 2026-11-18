import Yulang.GeneralDictionaryAggregateRows256
namespace Yulang.GeneralDictionaryHistoricalFields256
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralDictionaryAggregateHistory256 (history entry tree)
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralDictionaryLooseFamilyBase240 (source)
open GeneralDictionaryLooseIterationBook240 (context)

private theorem snoc_other (entries : List (Entry Nat)) (e : Entry Nat) (name : Nat)
 (different : e.1 ≠ name) : (mapping (entries ++ [e]) name).ty = (mapping entries name).ty := by
 rw [GeneralPresenceOrderedAppend256.mapping_append]
 have last : (mapping [e] name).ty = .var name :=
   GeneralPresenceOrderedSyntax247.mapping_outside [e] name (by intro other member; cases List.mem_singleton.mp member; exact different)
 rw [last]
 rfl

theorem past_expansion (n index : Nat) (before : index ≤ n) :
 (mapping (history n) (lower index)).ty = tree index := by
 induction n with
 | zero =>
   have same : index = 0 := by omega
   subst index
   rfl
 | succ n ih =>
   by_cases last : index = n+1
   · subst index; exact GeneralDictionaryAggregateHistory256.current_expansion (n+1)
   · change (mapping (history n ++ [entry n]) (lower index)).ty = _
     rw [snoc_other]
     · exact ih (by omega)
     · change lower (n+1) ≠ lower index
       intro equal
       have impossible := GeneralDictionaryLooseFamilyNames240.injective equal
       omega

theorem initial_name (n name : Nat) (small : name ≤ 4) :
 (mapping (history n) name).ty = .var name := by
 apply GeneralPresenceOrderedSyntax247.mapping_outside
 intro e member
 have above := GeneralDictionaryAggregateHistory256.targets_above n e member
 omega

def pool : List (TyTerm Nat) := [.var 0,.var 1,.var 2,.var 3,.var 4]

theorem variable_fixed (name : Nat) (small : name ≤ 4) :
 GeneralPresenceUnionNormal252.normalize pool (.var name) = .var name := by
 have cases : name = 0 ∨ name = 1 ∨ name = 2 ∨ name = 3 ∨ name = 4 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tree_fixed (n : Nat) : GeneralPresenceUnionNormal252.normalize pool (tree n) = .var 2 := by
 have same := GeneralPresenceNormalFinite252.union_atoms_same pool (tree n) (.var 2)
   (fun atom => (GeneralDictionaryAggregateHistory256.tree_atoms n atom).trans (by simp [GeneralPresenceUnionNormal252.atoms]))
 exact same.trans (variable_fixed 2 (by decide))

def representative (slot : Fin (n+5)) : Nat := if slot.val < 5 then slot.val else 2

theorem representative_small (slot : Fin (n+5)) : representative slot ≤ 4 := by
 unfold representative
 split <;> omega

theorem slot_fixed (n : Nat) (slot : Fin (n+5)) :
 GeneralPresenceUnionNormal252.normalize pool
   (((GeneralNominalRebaseRawView243.compile (context n).state (mapping (history n))).slot slot).ty) =
 .var (representative slot) := by
 change GeneralPresenceUnionNormal252.normalize pool (mapping (history n) (source n slot)).ty = _
 by_cases small : slot.val < 5
 · rw [GeneralDictionaryLooseFamilyBase240.source_small slot small,initial_name n slot.val (by omega),variable_fixed slot.val (by omega)]
   simp only [representative,small,ite_true]
 · rw [GeneralDictionaryLooseFamilyBase240.source_large slot (by omega),past_expansion n (slot.val-4) (by have bound := slot.isLt; omega),tree_fixed]
   simp only [representative,small,ite_false]

theorem slot_supported (n : Nat) (slot : Fin (n+5)) :
 GeneralPresenceUnionNormal252.atoms
   (((GeneralNominalRebaseRawView243.compile (context n).state (mapping (history n))).slot slot).ty) ⊆ pool := by
 change GeneralPresenceUnionNormal252.atoms (mapping (history n) (source n slot)).ty ⊆ pool
 by_cases small : slot.val < 5
 · rw [GeneralDictionaryLooseFamilyBase240.source_small slot small,initial_name n slot.val (by omega)]
   intro atom member
   cases List.mem_singleton.mp member
   have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 ∨ slot.val = 4 := by omega
   rcases cases with equal | equal | equal | equal | equal <;> simp [equal,pool]
 · rw [GeneralDictionaryLooseFamilyBase240.source_large slot (by omega),past_expansion n (slot.val-4) (by have bound := slot.isLt; omega)]
   intro atom member
   cases (GeneralDictionaryAggregateHistory256.tree_atoms _ atom).mp member
   simp [pool]

theorem slot_prepared (n : Nat) (slot : Fin (n+5)) :
 GeneralPresenceCheckedNormal252.prepare .lower pool
   (((GeneralNominalRebaseRawView243.compile (context n).state (mapping (history n))).slot slot).ty) =
 some (.var (representative slot)) :=
 (GeneralPresenceCheckedNormal252.prepare_exact ..).mpr ⟨slot_supported n slot,(slot_fixed n slot).symm⟩
end Yulang.GeneralDictionaryHistoricalFields256
