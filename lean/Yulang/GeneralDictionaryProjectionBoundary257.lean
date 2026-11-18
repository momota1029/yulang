import Yulang.GeneralDictionaryNoModelRefinement257
import Yulang.GeneralDictionaryLooseIterationNontermination240
namespace Yulang.GeneralDictionaryProjectionBoundary257
open GeneralDictionaryLooseFamilyBase240 (anchor original source)
open GeneralDictionaryFiveSlot257 (projection view)
open GeneralDictionaryLooseIterationIteration240 (state stages)

theorem anchor_distinct (n : Nat) : anchor (n+1) ≠ original (n+1) 2 := by
 intro equal
 have values := congrArg Fin.val equal
 change (if n+1=0 then 2 else n+1+4) = 2 at values
 simp only [Nat.add_one_ne_zero,ite_false] at values
 omega

theorem anchor_collapsed (n : Nat) : projection (anchor (n+1)) = projection (original (n+1) 2) := by
 rw [GeneralDictionaryFiveSlot257.original_projection]
 apply Fin.ext
 change (if (anchor (n+1)).val < 5 then (anchor (n+1)).val else 2) = 2
 have value : (anchor (n+1)).val = n+5 := by simp [anchor]
 rw [value]
 simp only [show ¬ n+5<5 by omega,ite_false]

theorem not_injective (n : Nat) : ¬ Function.Injective (@projection (n+1)) := by
 intro injective
 exact anchor_distinct n (injective (anchor_collapsed n))

theorem state_slots (n : Nat) : (state n).core.erased.current.context.state.base.slots = n+5 := by
 rw [(stages n).shape.current]

theorem states_distinct (a b : Nat) (different : a ≠ b) : state a ≠ state b := by
 intro equal
 have slots := congrArg (fun s => s.core.erased.current.context.state.base.slots) equal
 rw [state_slots,state_slots] at slots
 omega

/-- Infinitely many distinct actual states share the same compact current
view after the first cycle. The quotient is deliberately not a source-state
isomorphism, and no transition/certificate preservation is inferred. -/
theorem distinct_with_same_view (n : Nat) :
 state (n+1) ≠ state (n+2) ∧ view (n+1) = view (n+2) := by
 constructor
 · exact states_distinct _ _ (by omega)
 · rw [GeneralDictionaryFiveSlot257.stable n,GeneralDictionaryFiveSlot257.stable (n+1)]
end Yulang.GeneralDictionaryProjectionBoundary257
