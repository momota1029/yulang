import Yulang.SemilinearWeights

/-!
# Remove redundant finite semilinear syntax before decision procedures

Zero periods and duplicate period vectors are removed. Components are compared
by their base and their remaining period sets, so repetitions and permutations
of the same generators do not create extra automaton components. This is a
finite syntactic normalization, not a complete canonical form for semilinear
sets. Different generating sets may still denote the same monoid.

All decisions compare every coordinate of the finite integer vectors. The
proofs preserve the existing `Span` and `Meaning` predicates exactly, including
empty and zero-dimensional inputs.
-/

namespace Yulang.SemilinearNormalization

open SemilinearWeights

variable {n : Nat}

local instance : DecidableEq (Weight n) := fun left right =>
  decidable_of_iff (∀ coordinate, left coordinate = right coordinate) ⟨funext, congrFun⟩

def periods : List (Weight n) → List (Weight n)
  | [] => []
  | head :: rest =>
      let tail := periods rest
      if head = zero ∨ head ∈ tail then tail else head :: tail

theorem periods_membership (generators : List (Weight n)) (weight : Weight n) :
    weight ∈ periods generators ↔ weight ∈ generators ∧ weight ≠ zero := by
  induction generators generalizing weight with
  | nil => simp [periods]
  | cons head rest ih =>
      change (weight ∈ if head = zero ∨ head ∈ periods rest then periods rest else head :: periods rest) ↔ _
      by_cases removed : head = zero ∨ head ∈ periods rest
      · rw [ite_eq_left removed, ih, List.mem_cons]
        constructor
        · rintro ⟨member, nonzero⟩
          exact ⟨Or.inr member, nonzero⟩
        · rintro ⟨same | member, nonzero⟩
          · rw [same] at nonzero ⊢
            rcases removed with isZero | present
            · exact False.elim (nonzero isZero)
            · exact (ih head).mp present
          · exact ⟨member, nonzero⟩
      · rw [ite_eq_right removed, List.mem_cons, List.mem_cons, ih]
        have nonzero : head ≠ zero := fun equal => removed (Or.inl equal)
        constructor
        · rintro (rfl | ⟨member, unequal⟩)
          · exact ⟨Or.inl rfl, nonzero⟩
          · exact ⟨Or.inr member, unequal⟩
        · rintro ⟨rfl | member, unequal⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨member, unequal⟩

theorem periods_nodup (generators : List (Weight n)) : (periods generators).Nodup := by
  induction generators with
  | nil => simp [periods]
  | cons head rest ih =>
      unfold periods
      dsimp only
      split
      · exact ih
      · next retained => exact List.nodup_cons.mpr ⟨fun present => retained (Or.inr present), ih⟩

theorem periods_exclude_zero (generators : List (Weight n)) : zero ∉ periods generators := by
  intro present
  exact ((periods_membership generators zero).mp present).2 rfl

/-- Removing zero and repeated periods preserves all finite natural sums. -/
theorem span_exact (generators : List (Weight n)) (weight : Weight n) :
    Span (periods generators) weight ↔ Span generators weight := by
  constructor
  · exact span_mono (fun period member => ((periods_membership generators period).mp member).1)
  · intro member
    induction member with
    | nil => exact .nil
    | @cons head tail declared rest ih =>
        by_cases empty : head = zero
        · simpa only [empty, zero_add] using ih
        · exact .cons ((periods_membership generators head).mpr ⟨declared, empty⟩) ih

def line (original : Linear n) : Linear n := ⟨original.base, periods original.periods⟩

theorem line_exact (original : Linear n) (weight : Weight n) :
    (line original).Holds weight ↔ original.Holds weight := by
  simp only [line, Linear.Holds, span_exact]

def samePeriods (left right : List (Weight n)) : Bool :=
  left.all (fun period => decide (period ∈ right)) && right.all (fun period => decide (period ∈ left))

theorem samePeriods_exact (left right : List (Weight n)) :
    samePeriods left right = true ↔ ∀ period, period ∈ left ↔ period ∈ right := by
  simp only [samePeriods, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨forward, backward⟩ period => ⟨forward period, backward period⟩,
    fun same => ⟨fun period => (same period).mp, fun period => (same period).mpr⟩⟩

def sameLine (left right : Linear n) : Bool :=
  decide (left.base = right.base) && samePeriods left.periods right.periods

theorem sameLine_exact (left right : Linear n) : sameLine left right = true ↔
    left.base = right.base ∧ ∀ period, period ∈ left.periods ↔ period ∈ right.periods := by
  simp only [sameLine, Bool.and_eq_true, decide_eq_true_eq, samePeriods_exact]

theorem sameLine_refl (original : Linear n) : sameLine original original = true := by
  exact (sameLine_exact _ _).mpr ⟨rfl, fun _ => Iff.rfl⟩

theorem sameLine_sound (left right : Linear n) (same : sameLine left right = true)
    (weight : Weight n) : left.Holds weight ↔ right.Holds weight := by
  obtain ⟨bases, generators⟩ := (sameLine_exact left right).mp same
  have spans : ∀ offset, Span left.periods offset ↔ Span right.periods offset := fun _ =>
    ⟨span_mono (fun period => (generators period).mp),
      span_mono (fun period => (generators period).mpr)⟩
  simp only [Linear.Holds, bases, spans]

def normalize : Semi n → Semi n
  | [] => []
  | original :: rest =>
      let selected := line original
      let tail := normalize rest
      if tail.any (sameLine selected) then tail else selected :: tail

theorem meaning_cons (first : Linear n) (rest : Semi n) (weight : Weight n) :
    Meaning (first :: rest) weight ↔ first.Holds weight ∨ Meaning rest weight := by
  simp [Meaning]

/-- Duplicate components are discarded only after checking their same base
and the same finite generator set. Their period order does not matter. -/
theorem normalize_exact (semi : Semi n) (weight : Weight n) :
    Meaning (normalize semi) weight ↔ Meaning semi weight := by
  induction semi with
  | nil => rfl
  | cons original rest ih =>
      rw [meaning_cons]
      unfold normalize
      dsimp only
      split
      next duplicate =>
        obtain ⟨existing, present, same⟩ := List.any_eq_true.mp duplicate
        constructor
        · intro member
          exact Or.inr (ih.mp member)
        · rintro (member | member)
          · exact ⟨existing, present,
              (sameLine_sound _ _ same weight).mp ((line_exact original weight).mpr member)⟩
          · exact ih.mpr member
      next => rw [meaning_cons, line_exact, ih]

theorem normalize_periods (semi : Semi n) (component : Linear n)
    (present : component ∈ normalize semi) : component.periods.Nodup ∧ zero ∉ component.periods := by
  induction semi with
  | nil => simp [normalize] at present
  | cons original rest ih =>
      unfold normalize at present
      dsimp only at present
      split at present
      · exact ih present
      · rcases List.mem_cons.mp present with rfl | member
        · exact ⟨periods_nodup _, periods_exclude_zero _⟩
        · exact ih member

/-- Every retained component differs from all later components by its base or
its generator set. This is stronger than removing literally equal records. -/
theorem normalize_distinct (semi : Semi n) :
    (normalize semi).Pairwise (fun first second => sameLine first second = false) := by
  induction semi with
  | nil => simp [normalize]
  | cons original rest ih =>
      unfold normalize
      dsimp only
      split
      · exact ih
      · next noDuplicate =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih⟩
          intro existing present
          cases answer : sameLine (line original) existing with
          | false => rfl
          | true => exact False.elim (noDuplicate (List.any_eq_true.mpr ⟨existing, present, answer⟩))

end Yulang.SemilinearNormalization
