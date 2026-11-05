import Std

/-!
# Constructive semilinear closure for integer-weighted regular paths

Weights range over every coordinate of `Fin n → Int`; neither signs nor
magnitudes are bounded. A linear set is one base and finitely many generators,
and a semilinear set is a finite union of linear sets. Finite unions, Minkowski
sums and finite iteration have executable finite representations whose set
meanings are exact.

This module does not give a decision procedure for semilinear containment, or
remove point guards from a recursive row graph. In particular, commutative
reordering of path weights is used only after path legality has been expressed
by an unguarded regular expression.
-/

namespace Yulang.SemilinearWeights

abbrev Weight (n : Nat) := Fin n → Int
abbrev WeightSet (n : Nat) := Weight n → Prop

variable {n : Nat}

def zero : Weight n := fun _ => 0
def add (left right : Weight n) : Weight n := fun coordinate => left coordinate + right coordinate

@[simp] theorem zero_add (weight : Weight n) : add zero weight = weight := by
  funext coordinate
  simp [add, zero]

@[simp] theorem add_zero (weight : Weight n) : add weight zero = weight := by
  funext coordinate
  simp [add, zero]

theorem add_assoc (first second third : Weight n) :
    add (add first second) third = add first (add second third) := by
  funext coordinate
  simp [add, Int.add_assoc]

theorem add_comm (left right : Weight n) : add left right = add right left := by
  funext coordinate
  exact Int.add_comm _ _

theorem add_middle (first second third fourth : Weight n) :
    add (add first second) (add third fourth) = add (add first third) (add second fourth) := by
  funext coordinate
  simp only [add]
  omega

def Join (left right : WeightSet n) : WeightSet n := fun weight => left weight ∨ right weight

def Sum (left right : WeightSet n) : WeightSet n :=
  fun weight => ∃ first second, left first ∧ right second ∧ add first second = weight

/-- A finite sum of elements. No fuel bound or commutative path assumption is
part of this independent inductive meaning. -/
inductive Star (set : WeightSet n) : Weight n → Prop where
  | nil : Star set zero
  | cons {first rest} : set first → Star set rest → Star set (add first rest)

theorem Star.single {set : WeightSet n} {weight : Weight n} (member : set weight) :
    Star set weight := by
  simpa using Star.cons member (Star.nil : Star set zero)

theorem Star.append {set : WeightSet n} {first second : Weight n}
    (left : Star set first) (right : Star set second) : Star set (add first second) := by
  induction left with
  | nil => simpa using right
  | @cons head tail member rest ih => simpa [add_assoc] using Star.cons member ih

theorem Star.mono {left right : WeightSet n}
    (included : ∀ weight, left weight → right weight)
    {weight : Weight n} (member : Star left weight) : Star right weight := by
  induction member with
  | nil => exact .nil
  | cons first rest ih => exact .cons (included _ first) ih

theorem Star.congr {left right : WeightSet n}
    (same : ∀ weight, left weight ↔ right weight) (weight : Weight n) :
    Star left weight ↔ Star right weight :=
  ⟨Star.mono (fun weight => (same weight).mp), Star.mono (fun weight => (same weight).mpr)⟩

theorem star_join (left right : WeightSet n) (weight : Weight n) :
    Star (Join left right) weight ↔ Sum (Star left) (Star right) weight := by
  constructor
  · intro member
    induction member with
    | nil => exact ⟨zero, zero, .nil, .nil, zero_add _⟩
    | @cons head tail member rest ih =>
        obtain ⟨first, second, firstStar, secondStar, total⟩ := ih
        rcases member with leftHead | rightHead
        · refine ⟨add head first, second, .cons leftHead firstStar, secondStar, ?_⟩
          rw [add_assoc, total]
        · refine ⟨first, add head second, firstStar, .cons rightHead secondStar, ?_⟩
          rw [← add_assoc, add_comm first head, add_assoc, total]
  · rintro ⟨first, second, firstStar, secondStar, rfl⟩
    exact (firstStar.mono (fun _ member => Or.inl member)).append
      (secondStar.mono (fun _ member => Or.inr member))

def Span (generators : List (Weight n)) : WeightSet n := Star (fun weight => weight ∈ generators)

@[simp] theorem span_nil (weight : Weight n) : Span [] weight ↔ weight = zero := by
  constructor
  · intro member
    cases member with
    | nil => rfl
    | cons head tail => simp at head
  · rintro rfl
    exact .nil

theorem span_append (left right : List (Weight n)) (weight : Weight n) :
    Span (left ++ right) weight ↔ Sum (Span left) (Span right) weight := by
  have result := star_join (fun weight => weight ∈ left) (fun weight => weight ∈ right) weight
  unfold Join at result
  simpa only [Span, List.mem_append] using result

theorem span_mono {left right : List (Weight n)}
    (included : ∀ weight, weight ∈ left → weight ∈ right)
    {weight : Weight n} (member : Span left weight) : Span right weight :=
  member.mono included

structure Linear (n : Nat) where
  base : Weight n
  periods : List (Weight n)

def Linear.Holds (line : Linear n) : WeightSet n :=
  fun weight => ∃ offset, Span line.periods offset ∧ add line.base offset = weight

def Linear.point (weight : Weight n) : Linear n := ⟨weight, []⟩

@[simp] theorem Linear.point_exact (point weight : Weight n) :
    (Linear.point point).Holds weight ↔ point = weight := by
  simp [Holds, Linear.point]

def Linear.sum (left right : Linear n) : Linear n :=
  ⟨add left.base right.base, left.periods ++ right.periods⟩

theorem Linear.sum_exact (left right : Linear n) (weight : Weight n) :
    (left.sum right).Holds weight ↔ Sum left.Holds right.Holds weight := by
  constructor
  · rintro ⟨offset, member, total⟩
    obtain ⟨first, second, firstMember, secondMember, rfl⟩ :=
      (span_append left.periods right.periods offset).mp member
    refine ⟨add left.base first, add right.base second,
      ⟨first, firstMember, rfl⟩, ⟨second, secondMember, rfl⟩, ?_⟩
    rw [add_middle]
    exact total
  · rintro ⟨first, second, ⟨firstOffset, firstMember, rfl⟩,
      ⟨secondOffset, secondMember, rfl⟩, rfl⟩
    refine ⟨add firstOffset secondOffset,
      (span_append left.periods right.periods _).mpr
        ⟨firstOffset, secondOffset, firstMember, secondMember, rfl⟩, ?_⟩
    exact (add_middle left.base firstOffset right.base secondOffset).symm

abbrev Semi (n : Nat) := List (Linear n)

def Meaning (semi : Semi n) : WeightSet n :=
  fun weight => ∃ line ∈ semi, line.Holds weight

@[simp] theorem meaning_nil (weight : Weight n) : ¬ Meaning [] weight := by
  simp [Meaning]

@[simp] theorem meaning_singleton (line : Linear n) (weight : Weight n) :
    Meaning [line] weight ↔ line.Holds weight := by simp [Meaning]

theorem meaning_append (left right : Semi n) (weight : Weight n) :
    Meaning (left ++ right) weight ↔ Join (Meaning left) (Meaning right) weight := by
  simp only [Meaning, List.mem_append, Join]
  constructor
  · rintro ⟨line, member, fact⟩
    rcases member with member | member
    · exact Or.inl ⟨line, member, fact⟩
    · exact Or.inr ⟨line, member, fact⟩
  · rintro (⟨line, member, fact⟩ | ⟨line, member, fact⟩)
    · exact ⟨line, Or.inl member, fact⟩
    · exact ⟨line, Or.inr member, fact⟩

def sum (left right : Semi n) : Semi n :=
  left.flatMap fun first => right.map fun second => first.sum second

theorem sum_exact (left right : Semi n) (weight : Weight n) :
    Meaning (sum left right) weight ↔ Sum (Meaning left) (Meaning right) weight := by
  constructor
  · rintro ⟨line, member, fact⟩
    obtain ⟨first, firstMember, secondList⟩ := List.mem_flatMap.mp member
    obtain ⟨second, secondMember, rfl⟩ := List.mem_map.mp secondList
    obtain ⟨firstWeight, secondWeight, firstFact, secondFact, total⟩ :=
      (Linear.sum_exact first second weight).mp fact
    exact ⟨firstWeight, secondWeight, ⟨first, firstMember, firstFact⟩,
      ⟨second, secondMember, secondFact⟩, total⟩
  · rintro ⟨firstWeight, secondWeight, ⟨first, firstMember, firstFact⟩,
      ⟨second, secondMember, secondFact⟩, total⟩
    exact ⟨first.sum second, List.mem_flatMap.mpr
      ⟨first, firstMember, List.mem_map.mpr ⟨second, secondMember, rfl⟩⟩,
      (Linear.sum_exact first second weight).mpr ⟨firstWeight, secondWeight, firstFact, secondFact, total⟩⟩

/-- Zero repetitions, or at least one base followed by copies of the base and
the original periods. Periods become available only after that first base. -/
def Linear.star (line : Linear n) : Semi n :=
  [Linear.point zero, ⟨line.base, line.base :: line.periods⟩]

theorem Linear.star_positive (line : Linear n) {offset : Weight n}
    (member : Span (line.base :: line.periods) offset) :
    ∀ extra, Span line.periods extra → Star line.Holds (add line.base (add extra offset)) := by
  induction member with
  | nil =>
      intro extra extraMember
      simpa using Star.single (set := line.Holds) ⟨extra, extraMember, rfl⟩
  | @cons head tail member rest ih =>
      intro extra extraMember
      rcases List.mem_cons.mp member with rfl | period
      · have first : Star line.Holds (add line.base extra) :=
          Star.single ⟨extra, extraMember, rfl⟩
        have remaining := ih zero (Star.nil : Span line.periods zero)
        have combined := first.append remaining
        simpa only [zero_add, add_assoc] using combined
      · have nextExtra : Span line.periods (add extra head) :=
          extraMember.append (Star.single period)
        have result := ih (add extra head) nextExtra
        simpa only [add_assoc] using result

theorem Linear.star_exact (line : Linear n) (weight : Weight n) :
    Meaning line.star weight ↔ Star line.Holds weight := by
  have form : ∀ weight, Meaning line.star weight ↔
      weight = zero ∨ ∃ offset, Span (line.base :: line.periods) offset ∧ add line.base offset = weight := by
    intro weight
    simp [Meaning, Linear.star, Linear.Holds, Linear.point, eq_comm]
  rw [form]
  constructor
  · rintro (rfl | ⟨offset, member, rfl⟩)
    · exact .nil
    · simpa using line.star_positive member zero (Star.nil : Span line.periods zero)
  · intro member
    induction member with
    | nil => exact Or.inl rfl
    | @cons head tail first rest ih =>
        obtain ⟨offset, offsetMember, rfl⟩ := first
        have included : Span (line.base :: line.periods) offset :=
          span_mono (fun _ present => List.mem_cons_of_mem _ present) offsetMember
        rcases ih with rfl | ⟨tailOffset, tailMember, rfl⟩
        · exact Or.inr ⟨offset, included, (add_zero _).symm⟩
        · refine Or.inr ⟨add line.base (add offset tailOffset),
            Star.cons (List.mem_cons_self) (included.append tailMember), ?_⟩
          rw [← add_assoc, add_middle, add_assoc]

def star : Semi n → Semi n
  | [] => [Linear.point zero]
  | line :: rest => sum line.star (star rest)

theorem star_exact (semi : Semi n) (weight : Weight n) :
    Meaning (star semi) weight ↔ Star (Meaning semi) weight := by
  induction semi generalizing weight with
  | nil =>
      simp only [star, meaning_singleton, Linear.point_exact]
      constructor
      · rintro rfl
        exact .nil
      · intro member
        cases member with
        | nil => rfl
        | cons first rest => exact False.elim (meaning_nil _ first)
  | cons line rest ih =>
      rw [star, sum_exact]
      have setForm : ∀ weight, Meaning (line :: rest) weight ↔
          Join line.Holds (Meaning rest) weight := by
        intro weight
        simpa [Join] using meaning_append [line] rest weight
      rw [Star.congr setForm weight, star_join]
      unfold Sum
      simp only [Linear.star_exact, ih]

inductive Regex (n : Nat) where
  | empty
  | epsilon
  | atom (weight : Weight n)
  | union (left right : Regex n)
  | seq (left right : Regex n)
  | star (body : Regex n)

def Regex.Meaning : Regex n → WeightSet n
  | .empty => fun _ => False
  | .epsilon => fun weight => zero = weight
  | .atom point => fun weight => point = weight
  | .union left right => Join left.Meaning right.Meaning
  | .seq left right => Sum left.Meaning right.Meaning
  | .star body => Star body.Meaning

def Regex.compile : Regex n → Semi n
  | .empty => []
  | .epsilon => [Linear.point zero]
  | .atom weight => [Linear.point weight]
  | .union left right => left.compile ++ right.compile
  | .seq left right => sum left.compile right.compile
  | .star body => SemilinearWeights.star body.compile

theorem Regex.compile_exact (expression : Regex n) (weight : Weight n) :
    SemilinearWeights.Meaning expression.compile weight ↔ expression.Meaning weight := by
  induction expression generalizing weight with
  | empty => simp [compile, Meaning, SemilinearWeights.Meaning]
  | epsilon => simp [compile, Meaning]
  | atom point => simp [compile, Meaning]
  | union left right leftIH rightIH =>
      simp only [compile, meaning_append, Meaning, Join, leftIH, rightIH]
  | seq left right leftIH rightIH =>
      simp only [compile, sum_exact, Meaning, Sum, leftIH, rightIH]
  | star body ih =>
      rw [compile, star_exact, Meaning]
      exact Star.congr ih weight

end Yulang.SemilinearWeights
