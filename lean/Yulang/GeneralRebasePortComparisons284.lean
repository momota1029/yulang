import Yulang.GeneralRebaseWindowQueries284

namespace Yulang.GeneralRebasePortComparisons284
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans)
open GeneralRebaseWindowQueries284 (Invariant)
open GeneralRebaseLoopBase282 (equiv_trans)

def pair (r : Ty → Ty → Prop) : List Ty → Prop
  | [a,b] => r a b
  | _ => False

theorem invariant_pair {r : Ty → Ty → Prop}
    (stable : ∀ a b c d, Equivalent a c → Equivalent b d → (r a b ↔ r c d)) :
    Invariant (pair r) := by
  intro a b same
  cases same with
  | nil => exact Iff.rfl
  | cons first tail =>
    cases tail with
    | nil => exact Iff.rfl
    | cons second rest =>
      cases rest
      · exact stable _ _ _ _ first second
      · exact Iff.rfl

theorem invariant_eq : Invariant (pair Equivalent) := by
  apply invariant_pair
  intro a b c d ac bd
  exact ⟨fun ab => equiv_trans ⟨ac.2,ac.1⟩ (equiv_trans ab bd),
    fun cd => equiv_trans ac (equiv_trans cd ⟨bd.2,bd.1⟩)⟩

theorem invariant_le : Invariant (pair Subtype) := by
  apply invariant_pair
  intro a b c d ac bd
  exact ⟨fun ab => subtype_trans ac.2 (subtype_trans ab bd.1),
    fun cd => subtype_trans ac.1 (subtype_trans cd bd.2)⟩

end Yulang.GeneralRebasePortComparisons284
