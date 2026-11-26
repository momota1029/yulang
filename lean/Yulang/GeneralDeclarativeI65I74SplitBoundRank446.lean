import Yulang.GeneralDeclarativeI65I74SplitEscape446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SplitEscape446
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeWitnessRank350 (rank)

/-- Binary characteristic word over a fixed finite list. This avoids
enumerating SCCs: inclusion is monotone, and equal words agree at
every active name. -/
def bitValue (b : Bool) : Nat := if b then 1 else 0

def mask : List Nat → (Nat → Bool) → Nat
  | [],_ => 0
  | x::xs,p => 2 * mask xs p + bitValue (p x)

private theorem bit_le_one (b : Bool) : bitValue b ≤ 1 := by cases b <;> decide

private theorem bit_equal {a b : Bool} (h : bitValue a = bitValue b) : a = b := by
  cases a <;> cases b <;> simp_all [bitValue]

theorem mask_lt_two_power446 (xs : List Nat) (f : Nat → Bool) :
    mask xs f < 2 ^ xs.length := by
  induction xs with
  | nil => simp [mask]
  | cons a xs ih =>
    have range := bit_le_one (f a)
    simp only [mask,List.length_cons,Nat.pow_succ]
    omega

theorem mask_mono446 (xs : List Nat) (f g : Nat → Bool)
    (incl : ∀ x ∈ xs, f x = true → g x = true) : mask xs f ≤ mask xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have fst : bitValue (f x) ≤ bitValue (g x) := by
      cases h : f x
      · simp [bitValue]
      · rw [incl x List.mem_cons_self h]
        exact Nat.le_refl _
    have tail := ih (fun y inTail => incl y (List.mem_cons_of_mem _ inTail))
    simp only [mask]
    omega

theorem mask_eq_at_each_name446 (xs : List Nat) (f g : Nat → Bool)
    (same : mask xs f = mask xs g) :
    ∀ x ∈ xs, f x = g x := by
  induction xs with
  | nil => intro x absent; cases absent
  | cons a xs ih =>
    have l := bit_le_one (f a)
    have r := bit_le_one (g a)
    simp only [mask] at same
    have tail : mask xs f = mask xs g := by omega
    have front : bitValue (f a) = bitValue (g a) := by omega
    intro x here
    rcases List.mem_cons.mp here with atFront|inTail
    · subst x
      exact bit_equal front
    · exact ih tail x inTail

structure BoundSupport (s : GeneralDeclarativeWhere319.State) (limit : Nat) : Prop where
  interval : ∀ a b, (a,b) ∈ s.intervals → a < limit ∧ b < limit
  atom : ∀ a b, PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ s.ordinary →
    a < limit ∧ b < limit

theorem nontrivial_bound_inside_support446 {s : GeneralDeclarativeWhere319.State} {limit a b}
    (support : BoundSupport s limit) (h : Bound s a b) :
    a = b ∨ (a < limit ∧ b < limit) := by
  induction h with
  | interval found => exact .inr (support.interval _ _ found)
  | constraint found => exact .inr (support.atom _ _ found)
  | refl => exact .inl rfl
  | trans _ _ lo hi =>
    rcases lo with eq|left
    · simpa only [eq] using hi
    · rcases hi with eq|right
      · exact .inr ⟨left.1,eq ▸ left.2⟩
      · exact .inr ⟨left.1,right.2⟩

noncomputable def predBits (s : GeneralDeclarativeWhere319.State) (n : Nat) (x : Nat) : Bool := by
  classical
  exact decide (Bound s x n)

theorem pred_bits_exact446 {s : GeneralDeclarativeWhere319.State} {n x} :
    predBits s n x = true ↔ Bound s x n := by
  classical
  simp [predBits]

/-- Reserve grade 0 for inactive names. Each active grade encodes the
entire predecessor set of the original directed Bound relation. -/
noncomputable def boundGrades (s : GeneralDeclarativeWhere319.State) (limit : Nat) : List Nat :=
  List.ofFn fun i : Fin limit => 1 + mask (List.range limit) (predBits s i.val)

theorem rank_grade_inside446 {s : GeneralDeclarativeWhere319.State} {limit n}
    (inside : n < limit) :
    rank (boundGrades s limit) n = 1 + mask (List.range limit) (predBits s n) := by
  simp [rank,boundGrades,inside]

theorem rank_grade_outside446 {s : GeneralDeclarativeWhere319.State} {limit n}
    (outside : limit ≤ n) : rank (boundGrades s limit) n = 0 := by
  simp [rank,boundGrades,Nat.not_lt_of_ge outside]

theorem bound_grade_monotone446 {s : GeneralDeclarativeWhere319.State} {limit a b}
    (support : BoundSupport s limit) (h : Bound s a b) :
    rank (boundGrades s limit) a ≤ rank (boundGrades s limit) b := by
  rcases nontrivial_bound_inside_support446 support h with same|⟨la,lb⟩
  · subst b
    exact Nat.le_refl _
  · rw [rank_grade_inside446 la,rank_grade_inside446 lb]
    apply Nat.add_le_add_left
    apply mask_mono446
    intro x _ active
    exact pred_bits_exact446.mpr (.trans (pred_bits_exact446.mp active) h)

theorem equal_active_grades_are_exact_SCC446 {s : GeneralDeclarativeWhere319.State} {limit a b}
    (lo : a < limit) (hi : b < limit)
    (same : rank (boundGrades s limit) a = rank (boundGrades s limit) b) :
    Bound s a b ∧ Bound s b a := by
  rw [rank_grade_inside446 lo,rank_grade_inside446 hi] at same
  have all := mask_eq_at_each_name446 (List.range limit) (predBits s a) (predBits s b)
    (Nat.add_left_cancel same)
  have aa : predBits s a a = true := pred_bits_exact446.mpr (.refl a)
  have bb : predBits s b b = true := pred_bits_exact446.mpr (.refl b)
  exact ⟨pred_bits_exact446.mp ((all a (List.mem_range.mpr lo)).symm.trans aa),
    pred_bits_exact446.mp ((all b (List.mem_range.mpr hi)).trans bb)⟩

theorem active_grade_bounded446 {s : GeneralDeclarativeWhere319.State} {limit a}
    (inside : a < limit) :
    rank (boundGrades s limit) a < 2 ^ limit + 1 := by
  rw [rank_grade_inside446 inside]
  have bound := mask_lt_two_power446 (List.range limit) (predBits s a)
  rw [List.length_range] at bound
  omega

end Yulang.GeneralDeclarativeI65.I72.SplitEscape446
