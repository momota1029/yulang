import Yulang.GeneralDictionaryVersionLoopNext237
/-! Arithmetic allocation family suggested by the verified finite retarget
prefix. These statements concern names only; no kernel trace indexed by all
natural numbers, infinite execution, or termination refutation is asserted. -/
namespace Yulang.GeneralDictionaryVersionLoopNames238
open GeneralNominalAggregateVersion231
open GeneralNominalAllocation (Bindings)
def repeated (source : Nat) : Bindings := [(0,source,source),(0,source,source)]
def lower : Nat → Nat
 | 0 => 2
 | n+1 => slot 3 0 0 0 0 (repeated (lower n))
def upper (n : Nat) : Nat := slot 3 0 0 1 0 (repeated (lower n))
theorem increases (n) : lower n < lower (n+1) :=
 (GeneralNominalVersionedDependency236.endpoints_below_slot 3 0 0 0 0 (repeated (lower n))
   (by exact List.mem_cons_self : (lower n,lower n) ∈ GeneralNominalAllocation.occurrences (repeated (lower n)) 0)).1

theorem strict {a b : Nat} (ordered : a < b) : lower a < lower b := by
 induction b with
 | zero => omega
 | succ b ih =>
   by_cases same : a=b
   · subst a; exact increases b
   · exact Nat.lt_trans (ih (by omega)) (increases b)

theorem injective {a b} (same : lower a = lower b) : a = b := by
 by_cases equal : a = b
 · exact equal
 · rcases Nat.lt_or_gt_of_ne equal with ordered | ordered
   · have := strict ordered; omega
   · have := strict ordered; omega

theorem upper_injective {a b} (same : upper a = upper b) : a = b := by
 have occurrences := (slot_eq_iff 3 0 0 1 0).mp same
 have endpoint := congrArg (fun values : List (Nat × Nat) => values.head?.map Prod.fst) occurrences
 have equal : lower a = lower b := Option.some.inj endpoint
 exact injective equal

theorem separate (a b) : lower (a+1) ≠ upper b :=
 distinct_purpose 3 0 0 0 1 0 _ _ (by decide)

theorem lower_above (n) : 3 < lower (n+1) := above_seed ..
theorem upper_above (n) : 3 < upper n := above_seed ..

theorem first_lower : lower 1 = GeneralDictionaryVersionLoopPacket237.lo := rfl
theorem first_upper : upper 0 = GeneralDictionaryVersionLoopPacket237.hi := rfl
theorem second_lower : lower 2 = GeneralDictionaryVersionLoopNext237.nextLo := rfl
theorem second_upper : upper 1 = GeneralDictionaryVersionLoopNext237.nextHi := rfl
end Yulang.GeneralDictionaryVersionLoopNames238
