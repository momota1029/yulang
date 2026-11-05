import Yulang.SemilinearWeights

/-!
# Binary coefficients for arbitrary signed integer generators

Membership in the nonnegative span of finitely many integer vectors is
equivalent to a finite binary-carry computation. Generator coordinates may be
negative and generators may cancel. Coefficients remain natural numbers.

The lemmas here expose the arithmetic independently of the finite-state
decision procedure. They do not bound coefficients or the number of digits.
-/

namespace Yulang.BinaryCarries

open SemilinearWeights

variable {n : Nat}

def scale (count : Nat) (weight : Weight n) : Weight n :=
  fun coordinate => (count : Int) * weight coordinate

@[simp] theorem scale_zero (weight : Weight n) : scale 0 weight = zero := by
  funext coordinate
  simp [scale, zero]

@[simp] theorem scale_one (weight : Weight n) : scale 1 weight = weight := by
  funext coordinate
  simp [scale]

theorem scale_succ (count : Nat) (weight : Weight n) :
    scale (count + 1) weight = add weight (scale count weight) := by
  funext coordinate
  simp [scale, add, Int.add_mul, Int.add_comm]

theorem scale_span (generators : List (Weight n)) (count : Nat) (weight : Weight n)
    (member : Span generators weight) : Span generators (scale count weight) := by
  induction count with
  | zero => rw [scale_zero]; exact Star.nil
  | succ count ih => rw [scale_succ]; exact member.append ih

theorem singleton_span (generator weight : Weight n) :
    Span [generator] weight ↔ ∃ count, scale count generator = weight := by
  constructor
  · intro member
    induction member with
    | nil => exact ⟨0, scale_zero _⟩
    | @cons head tail present member ih =>
        have same : head = generator := List.mem_singleton.mp present
        obtain ⟨count, rfl⟩ := ih
        subst head
        exact ⟨count + 1, scale_succ _ _⟩
  · rintro ⟨count, rfl⟩
    exact scale_span _ _ _ (Star.single (by simp))

def combine : List (Weight n) → List Nat → Weight n
  | generator :: rest, count :: counts => add (scale count generator) (combine rest counts)
  | _, _ => zero

theorem combine_span (generators : List (Weight n)) (counts : List Nat) :
    Span generators (combine generators counts) := by
  induction generators generalizing counts with
  | nil => cases counts <;> exact .nil
  | cons generator rest ih =>
      cases counts with
      | nil => exact .nil
      | cons count counts =>
          exact (scale_span _ count _ (Star.single (List.mem_cons_self))).append
            (span_mono (fun _ h => List.mem_cons_of_mem _ h) (ih counts))

theorem span_coefficients (generators : List (Weight n)) (weight : Weight n)
    (member : Span generators weight) :
    ∃ counts, counts.length = generators.length ∧ combine generators counts = weight := by
  induction generators generalizing weight with
  | nil =>
      have same := (span_nil weight).mp member
      exact ⟨[], rfl, same.symm⟩
  | cons generator rest ih =>
      obtain ⟨first, tail, firstSpan, tailSpan, total⟩ :=
        (span_append [generator] rest weight).mp member
      obtain ⟨count, rfl⟩ := (singleton_span generator first).mp firstSpan
      obtain ⟨counts, length, rfl⟩ := ih tail tailSpan
      exact ⟨count :: counts, by simp [length], total⟩

def digits : List (Weight n) → List (Weight n)
  | [] => [zero]
  | generator :: rest => digits rest ++ (digits rest).map (add generator)

theorem zero_digit (generators : List (Weight n)) : zero ∈ digits generators := by
  induction generators with
  | nil => simp [digits]
  | cons generator rest ih => exact List.mem_append_left _ ih

theorem digit_span (generators : List (Weight n)) (digit : Weight n)
    (member : digit ∈ digits generators) : Span generators digit := by
  induction generators generalizing digit with
  | nil => have same : digit = zero := List.mem_singleton.mp member; subst digit; exact .nil
  | cons generator rest ih =>
      rcases List.mem_append.mp member with direct | added
      · exact span_mono (fun _ h => List.mem_cons_of_mem _ h) (ih digit direct)
      · obtain ⟨tail, present, rfl⟩ := List.mem_map.mp added
        exact Star.cons List.mem_cons_self
          (span_mono (fun _ h => List.mem_cons_of_mem _ h) (ih tail present))

theorem coefficient_digit (generators : List (Weight n)) (counts : List Nat)
    (length : counts.length = generators.length) :
    combine generators (counts.map (fun count => count % 2)) ∈ digits generators := by
  induction generators generalizing counts with
  | nil => cases counts <;> simp_all [combine, digits]
  | cons generator rest ih =>
      cases counts with
      | nil => simp at length
      | cons count counts =>
          have restLength : counts.length = rest.length := by simpa using length
          have tail := ih counts restLength
          have choices : count % 2 = 0 ∨ count % 2 = 1 := by omega
          rcases choices with even | odd
          · simpa [combine, digits, even] using List.mem_append_left
              ((digits rest).map (add generator)) tail
          · apply List.mem_append_right
            exact List.mem_map.mpr ⟨combine rest (counts.map (fun count => count % 2)), tail,
              by simp [combine, odd]⟩

theorem coefficient_split (generators : List (Weight n)) (counts : List Nat) :
    combine generators counts =
      add (combine generators (counts.map (fun count => count % 2)))
        (scale 2 (combine generators (counts.map (fun count => count / 2)))) := by
  induction generators generalizing counts with
  | nil => cases counts <;> funext coordinate <;> simp [combine, add, scale, zero]
  | cons generator rest ih =>
      cases counts with
      | nil => funext coordinate; simp [combine, add, scale, zero]
      | cons count counts =>
          have split : (count : Int) = (count % 2 : Nat) + 2 * (count / 2 : Nat) := by omega
          funext coordinate
          have tail := congrFun (ih counts) coordinate
          simp only [combine, List.map_cons, add, scale] at tail ⊢
          rw [split, Int.add_mul, Int.mul_assoc]
          omega

theorem halved_sum_le (counts : List Nat) :
    (counts.map (fun count => count / 2)).sum ≤ counts.sum := by
  induction counts with
  | nil => simp
  | cons count counts ih => simp only [List.map_cons, List.sum_cons]; omega

theorem halved_sum_lt (counts : List Nat) (positive : 0 < counts.sum) :
    (counts.map (fun count => count / 2)).sum < counts.sum := by
  induction counts with
  | nil => simp at positive
  | cons count counts ih =>
      have weak := halved_sum_le counts
      by_cases headPositive : 0 < count
      · simp only [List.map_cons, List.sum_cons]; omega
      · have tailPositive : 0 < counts.sum := by simpa [show count = 0 by omega] using positive
        have strict := ih tailPositive
        simp only [List.map_cons, List.sum_cons]
        omega

theorem combine_sum_zero (generators : List (Weight n)) (counts : List Nat)
    (empty : counts.sum = 0) : combine generators counts = zero := by
  induction generators generalizing counts with
  | nil => cases counts <;> rfl
  | cons generator rest ih =>
      cases counts with
      | nil => rfl
      | cons count counts =>
          have head : count = 0 := by simp only [List.sum_cons] at empty; omega
          have tail : counts.sum = 0 := by simp only [List.sum_cons] at empty; omega
          simp [combine, head, ih counts tail]

def norm (weight : Weight n) : Nat :=
  (List.ofFn fun coordinate => (weight coordinate).natAbs).sum

private theorem member_le_sum (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.sum := by
  induction values with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have prior := ih member; simp only [List.sum_cons]; omega

theorem coordinate_le_norm (weight : Weight n) (coordinate : Fin n) :
    (weight coordinate).natAbs ≤ norm weight :=
  member_le_sum _ _ (List.mem_ofFn.mpr ⟨coordinate, rfl⟩)

def Within (bound : Nat) (weight : Weight n) : Prop :=
  ∀ coordinate, -(bound : Int) ≤ weight coordinate ∧ weight coordinate ≤ bound

theorem within_norm (weight : Weight n) : Within (norm weight) weight := by
  intro coordinate
  have bound := coordinate_le_norm weight coordinate
  have positive := Int.le_natAbs (a := weight coordinate)
  have negative := Int.le_natAbs (a := -(weight coordinate))
  simp only [Int.natAbs_neg] at negative
  omega

theorem Within.mono {small large : Nat} {weight : Weight n}
    (bounded : Within small weight) (included : small ≤ large) : Within large weight := by
  intro coordinate
  have both := bounded coordinate
  omega

def budget (generators : List (Weight n)) : Nat := (generators.map norm).sum

theorem digit_bounded (generators : List (Weight n)) (digit : Weight n)
    (member : digit ∈ digits generators) : Within (budget generators) digit := by
  induction generators generalizing digit with
  | nil =>
      have same : digit = zero := List.mem_singleton.mp member
      subst digit
      simp [Within, budget, zero]
  | cons generator rest ih =>
      rcases List.mem_append.mp member with direct | added
      · have prior := ih digit direct
        apply prior.mono
        simp [budget]
      · obtain ⟨tail, present, rfl⟩ := List.mem_map.mp added
        have head := within_norm generator
        have remainder := ih tail present
        intro coordinate
        have h := head coordinate
        have t := remainder coordinate
        simp only [budget, List.map_cons, List.sum_cons, Int.natCast_add, add] at *
        omega

/-- A binary step preserves the finite carry box. The proof applies to every
signed generator and does not assume that coefficients or carries are positive. -/
theorem step_bounded (generators : List (Weight n)) (bound : Nat)
    (large : budget generators ≤ bound) (current digit next : Weight n)
    (bounded : Within bound current) (selected : digit ∈ digits generators)
    (step : current = add digit (scale 2 next)) : Within bound next := by
  have digitBound := (digit_bounded generators digit selected).mono large
  intro coordinate
  have before := bounded coordinate
  have chosen := digitBound coordinate
  have equality := congrFun step coordinate
  simp only [add, scale] at equality
  omega

end Yulang.BinaryCarries
