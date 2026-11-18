import Yulang.GeneralDictionaryUpperHistory257
namespace Yulang.GeneralDictionaryFullExpansion257
open Core.PresenceGeneration
open GeneralDictionaryUpperHistory257 (history lowerEntry upperEntry)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralDictionaryAggregateHistory256 (tree)

theorem snoc_other (entries : List (Entry Nat)) (e : Entry Nat) (name : Nat)
 (different : e.1 ≠ name) : (mapping (entries ++ [e]) name).ty = (mapping entries name).ty := by
 rw [GeneralPresenceOrderedAppend256.mapping_append]
 have last : (mapping [e] name).ty = .var name :=
   GeneralPresenceOrderedSyntax247.mapping_outside [e] name (by intro other member; cases List.mem_singleton.mp member; exact different)
 rw [last]
 rfl

theorem current_lower (n : Nat) : (mapping (history n) (lower n)).ty = tree n := by
 induction n with
 | zero => rfl
 | succ n ih =>
   change (mapping (history n ++ [lowerEntry n,upperEntry n]) (lower (n+1))).ty = _
   rw [show history n ++ [lowerEntry n,upperEntry n] = (history n ++ [lowerEntry n]) ++ [upperEntry n] by simp]
   rw [snoc_other _ _ _ (Ne.symm (GeneralDictionaryLooseFamilyNames240.separate n n))]
   change (mapping (history n ++ [lowerEntry n]) (lowerEntry n).1).ty = _
   rw [GeneralPresenceOrderedAppend256.mapping_snoc]
   change TyTerm.union (mapping (history n) (lower n)).ty (mapping (history n) (lower n)).ty = _
   rw [ih]
   rfl

theorem past_lower (n index : Nat) (before : index ≤ n) :
 (mapping (history n) (lower index)).ty = tree index := by
 induction n with
 | zero => have same : index = 0 := by omega
           subst index; rfl
 | succ n ih =>
   by_cases last : index = n+1
   · subst index; exact current_lower (n+1)
   · change (mapping (history n ++ [lowerEntry n,upperEntry n]) (lower index)).ty = _
     rw [show history n ++ [lowerEntry n,upperEntry n] = (history n ++ [lowerEntry n]) ++ [upperEntry n] by simp]
     have separate : (upperEntry n).1 ≠ lower index := by
       cases index with
       | zero => have above := GeneralDictionaryLooseFamilyNames240.upper_above n; change upper n ≠ 2; omega
       | succ k => exact Ne.symm (GeneralDictionaryLooseFamilyNames240.separate k n)
     rw [snoc_other _ _ _ separate,snoc_other]
     · exact ih (by omega)
     · change lower (n+1) ≠ lower index
       intro equal
       have impossible := GeneralDictionaryLooseFamilyNames240.injective equal
       omega

theorem current_upper (n : Nat) :
 (mapping (history (n+1)) (upper n)).ty = .inter (.var 4) (.var 4) := by
 change (mapping (history n ++ [lowerEntry n,upperEntry n]) (upper n)).ty = _
 rw [show history n ++ [lowerEntry n,upperEntry n] = (history n ++ [lowerEntry n]) ++ [upperEntry n] by simp]
 change (mapping ((history n ++ [lowerEntry n]) ++ [upperEntry n]) (upperEntry n).1).ty = _
 rw [GeneralPresenceOrderedAppend256.mapping_snoc]
 change TyTerm.inter (mapping (history n ++ [lowerEntry n]) 4).ty (mapping (history n ++ [lowerEntry n]) 4).ty = _
 have diff : (lowerEntry n).1 ≠ 4 := by have above := GeneralDictionaryLooseFamilyNames240.lower_above n; exact Nat.ne_of_gt above
 rw [snoc_other _ _ _ diff,GeneralDictionaryUpperHistory257.initial_fixed n 4 (by decide)]

theorem past_upper (n index : Nat) (before : index < n) :
 (mapping (history n) (upper index)).ty = .inter (.var 4) (.var 4) := by
 induction n with
 | zero => omega
 | succ n ih =>
   by_cases last : index = n
   · subst index; exact current_upper n
   · change (mapping (history n ++ [lowerEntry n,upperEntry n]) (upper index)).ty = _
     rw [show history n ++ [lowerEntry n,upperEntry n] = (history n ++ [lowerEntry n]) ++ [upperEntry n] by simp]
     have different : (upperEntry n).1 ≠ upper index := by
       intro equal
       have impossible := GeneralDictionaryLooseFamilyNames240.upper_injective equal
       omega
     rw [snoc_other _ _ _ different,snoc_other _ _ _ (GeneralDictionaryLooseFamilyNames240.separate n index)]
     exact ih (by omega)
end Yulang.GeneralDictionaryFullExpansion257
