import Yulang.CommonRoleStructuralConflicts

/-! Recursive rigid conflicts inside pairs, arrows and equal-tag variants.
This is a refutation fragment, not a complete subtype decision procedure. -/
namespace Yulang.CommonRoleRecursiveConflicts
open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonRoleStructuralConflicts (Mismatch mismatch mismatch_exact mismatch_no_subtype)

inductive Refutes : TyTerm α → TyTerm α → Prop where
  | head : Mismatch l r → Refutes l r
  | pairLeft : Refutes a c → Refutes (.pair a b) (.pair c d)
  | pairRight : Refutes b d → Refutes (.pair a b) (.pair c d)
  | arrowArg : Refutes c a → Refutes (.arrow a ea b eb) (.arrow c ec d ed)
  | arrowResult : Refutes b d → Refutes (.arrow a ea b eb) (.arrow c ec d ed)
  | variant : Refutes a b → Refutes (.variant tag a) (.variant tag b)

theorem refutes_no_subtype (l r : TyTerm α) (h : Refutes l r) (ρ : α → Comp Common.model) :
    ¬ Common.Subtype (l.eval Common.model ρ) (r.eval Common.model ρ) := by
  induction h with
  | head h => exact mismatch_no_subtype _ _ h ρ
  | pairLeft _ ih =>
    intro h; exact ih ((Common.common_pair_iff ..).mp h).1
  | pairRight _ ih =>
    intro h; exact ih ((Common.common_pair_iff ..).mp h).2
  | arrowArg _ ih =>
    intro h; exact ih ((Common.common_arrow_iff ..).mp h).1
  | arrowResult _ ih =>
    intro h; exact ih ((Common.common_arrow_iff ..).mp h).2.2.1
  | variant _ ih =>
    intro h; exact ih ((Common.common_variant_iff ..).mp h)

def weight : TyTerm α → Nat
  | .pair a b | .arrow a _ b _ | .union a b | .inter a b
  | .record _ a b | .recordDefault _ a b => weight a + weight b + 1
  | .variant _ a | .required _ a => weight a + 1
  | _ => 1

def checkFuel : Nat → TyTerm α → TyTerm α → Bool
  | 0, _, _ => false
  | k+1, l, r => mismatch l r || match l,r with
    | .pair a b, .pair c d => checkFuel k a c || checkFuel k b d
    | .arrow a _ b _, .arrow c _ d _ => checkFuel k c a || checkFuel k b d
    | .variant i a, .variant j b => if i = j then checkFuel k a b else false
    | _, _ => false

theorem fuel_sound (k : Nat) (l r : TyTerm α) :
    checkFuel k l r = true → Refutes l r := by
  induction k generalizing l r with
  | zero => simp [checkFuel]
  | succ k ih =>
    intro h
    simp only [checkFuel, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .head ((mismatch_exact ..).mp h)
    · split at h
      · simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact .pairLeft (ih _ _ h)
        · exact .pairRight (ih _ _ h)
      · simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact .arrowArg (ih _ _ h)
        · exact .arrowResult (ih _ _ h)
      · split at h
        · rename_i eq; subst eq
          exact .variant (ih _ _ h)
        · contradiction
      · contradiction

theorem weight_positive (t : TyTerm α) : 0 < weight t := by
  cases t <;> simp [weight] <;> omega

theorem fuel_complete (h : Refutes l r) (k : Nat)
    (enough : weight l + weight r ≤ k) : checkFuel k l r = true := by
  induction h generalizing k with
  | @head l r h =>
    cases k with
    | zero => have pos := weight_positive l
              omega
    | succ k => simp only [checkFuel, Bool.or_eq_true]; exact Or.inl ((mismatch_exact ..).mpr h)
  | pairLeft h ih =>
    cases k with
    | zero => simp [weight] at enough
    | succ k =>
      simp only [checkFuel, Bool.or_eq_true]
      exact Or.inr (Or.inl (ih k (by simp [weight] at enough; omega)))
  | pairRight h ih =>
    cases k with
    | zero => simp [weight] at enough
    | succ k =>
      simp only [checkFuel, Bool.or_eq_true]
      exact Or.inr (Or.inr (ih k (by simp [weight] at enough; omega)))
  | arrowArg h ih =>
    cases k with
    | zero => simp [weight] at enough
    | succ k =>
      simp only [checkFuel, Bool.or_eq_true]
      exact Or.inr (Or.inl (ih k (by simp [weight] at enough; omega)))
  | arrowResult h ih =>
    cases k with
    | zero => simp [weight] at enough
    | succ k =>
      simp only [checkFuel, Bool.or_eq_true]
      exact Or.inr (Or.inr (ih k (by simp [weight] at enough; omega)))
  | variant h ih =>
    cases k with
    | zero => simp [weight] at enough
    | succ k =>
      simp only [checkFuel, Bool.or_eq_true]
      exact Or.inr (ih k (by simp [weight] at enough; omega))

def check (l r : TyTerm α) : Bool := checkFuel (weight l + weight r) l r

theorem check_exact (l r : TyTerm α) : check l r = true ↔ Refutes l r :=
  ⟨fuel_sound _ l r, fun h => fuel_complete h _ (Nat.le_refl _)⟩

theorem checked_no_subtype (l r : TyTerm α) (h : check l r = true)
    (ρ : α → Comp Common.model) :
    ¬ Common.Subtype (l.eval Common.model ρ) (r.eval Common.model ρ) :=
  refutes_no_subtype l r ((check_exact ..).mp h) ρ

/-- Inner scalar disagreement is detected despite equal outer pair heads. -/
theorem nested_pair_checked (a b : TyTerm α) :
    check (.pair (.base .int) a) (.pair (.base .bool) b) = true := by
  apply (check_exact ..).mpr
  exact .pairLeft (.head ((mismatch_exact ..).mp (by rfl)))

theorem nested_pair_old_mismatch_false (a b : TyTerm α) :
    mismatch (.pair (.base .int) a) (.pair (.base .bool) b) = false := by
  rfl

/-- Arrow arguments are checked in the reverse direction. -/
theorem arrow_contravariant_checked (a b : TyTerm α) (ea eb ec ed : RowTerm α) :
    check (.arrow .bottom ea a eb) (.arrow (.base .int) ec b ed) = true := by
  apply (check_exact ..).mpr
  exact .arrowArg (.head ((mismatch_exact ..).mp (by rfl)))

end Yulang.CommonRoleRecursiveConflicts
