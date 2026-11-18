import Yulang.GeneralDictionaryFullExpansion257
import Yulang.GeneralPresenceIdempotentTree257
namespace Yulang.GeneralDictionaryFullReduced257
open Core.PresenceGeneration
open GeneralDictionaryUpperHistory257 (history)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceIdempotentTree257 (reduce join meet)
open GeneralDictionaryAggregateHistory256 (tree)

theorem reduce_tree (n : Nat) : reduce (tree n) = .var 2 := by
 induction n with
 | zero => rfl
 | succ n ih => simp only [tree,reduce,ih,join,ite_true]

theorem lower_fixed (n index : Nat) (before : index ≤ n) :
 reduce (mapping (history n) (lower index)).ty = .var 2 := by
 rw [GeneralDictionaryFullExpansion257.past_lower n index before,reduce_tree]

theorem upper_fixed (n index : Nat) (before : index < n) :
 reduce (mapping (history n) (upper index)).ty = .var 4 := by
 rw [GeneralDictionaryFullExpansion257.past_upper n index before]
 rfl

theorem initial_fixed (n name : Nat) (small : name ≤ 4) :
 reduce (mapping (history n) name).ty = .var name := by
 rw [GeneralDictionaryUpperHistory257.initial_fixed n name small]
 rfl

/-- A one-sided adapter cannot silently drop the opposite connective, even
for this exact upper definition extracted from the actual retained history. -/
theorem lower_adapter_failure (n index : Nat) (before : index < n) :
 GeneralPresenceCheckedNormal252.prepare .lower [.var 0,.var 1,.var 2,.var 3,.var 4]
   (mapping (history n) (upper index)).ty = none := by
 rw [GeneralDictionaryFullExpansion257.past_upper n index before]
 rfl

theorem repaired_upper_prepare (n index : Nat) (before : index < n) :
 GeneralPresenceCheckedNormal252.prepare .lower [.var 0,.var 1,.var 2,.var 3,.var 4]
   (reduce (mapping (history n) (upper index)).ty) = some (.var 4) := by
 rw [upper_fixed n index before]
 rfl
end Yulang.GeneralDictionaryFullReduced257
