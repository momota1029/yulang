import Std

namespace Yulang.GeneralRebasePartialBool268

abbrev Answer := Option Bool

/-- An unknown computation does not assert either truth value. -/
def Reflect (p : Prop) : Answer → Prop
 | none => True
 | some true => p
 | some false => ¬ p

def neg : Answer → Answer
 | none => none
 | some b => some (!b)

def either : Answer → Answer → Answer
 | some true, _ => some true
 | _, some true => some true
 | some false, some false => some false
 | _, _ => none

def both (a b : Answer) : Answer := neg (either (neg a) (neg b))

theorem neg_sound {p : Prop} {a : Answer} (valid : Reflect p a) :
 Reflect (¬ p) (neg a) := by
 cases a with
 | none => trivial
 | some b =>
   cases b
   · exact valid
   · exact fun h => h valid

theorem either_sound {p q : Prop} {a b : Answer} (one : Reflect p a) (two : Reflect q b) :
 Reflect (p ∨ q) (either a b) := by
 cases a with
 | none =>
   cases b with
   | none => trivial
   | some y =>
     cases y
     · trivial
     · exact Or.inr two
 | some x =>
   cases x
   · cases b with
     | none => trivial
     | some y =>
       cases y
       · exact fun h => h.elim one two
       · exact Or.inr two
   · exact Or.inl one

theorem both_sound {p q : Prop} {a b : Answer} (one : Reflect p a) (two : Reflect q b) :
 Reflect (p ∧ q) (both a b) := by
 have valid := neg_sound (either_sound (neg_sound one) (neg_sound two))
 cases h : both a b with
 | none => trivial
 | some result =>
   change Reflect (¬ (¬ p ∨ ¬ q)) (both a b) at valid
   rw [h] at valid
   cases result
   · exact fun both => valid (fun proof => proof.elim (fun notP => notP both.1) (fun notQ => notQ both.2))
   · exact ⟨Classical.byContradiction (fun no => valid (Or.inl no)),
            Classical.byContradiction (fun no => valid (Or.inr no))⟩

theorem total_neg {a : Answer} (known : a ≠ none) : neg a ≠ none := by
 cases a with
 | none => exact False.elim (known rfl)
 | some b => simp [neg]

theorem total_either {a b : Answer} (one : a ≠ none) (two : b ≠ none) : either a b ≠ none := by
 cases a with
 | none => exact False.elim (one rfl)
 | some x =>
   cases b with
   | none => exact False.elim (two rfl)
   | some y => cases x <;> cases y <;> decide

theorem total_both {a b : Answer} (one : a ≠ none) (two : b ≠ none) : both a b ≠ none :=
 total_neg (total_either (total_neg one) (total_neg two))

theorem true_iff {p : Prop} {a : Answer} (valid : Reflect p a) (known : a ≠ none) :
 a = some true ↔ p := by
 cases a with
 | none => exact False.elim (known rfl)
 | some b =>
   cases b
   · constructor
     · intro eq; cases eq
     · intro hp; exact False.elim (valid hp)
   · exact ⟨fun _ => valid,fun _ => rfl⟩

end Yulang.GeneralRebasePartialBool268
