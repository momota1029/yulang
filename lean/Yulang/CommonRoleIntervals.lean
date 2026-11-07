import Yulang.CommonBoundCoalescing
import Yulang.DemandBoundPropagation

/-!
# Centerless role-argument intervals over the existing Common carrier

An interval is just two endpoints. The actual type in `Fits` is a semantic
argument, not a stored center or a point chosen by a resolver. Reconciliation
uses Common's existing join/meet and emits existing template checks. These
theorems do not yet define candidate eligibility or role resolution.
-/

namespace Yulang.CommonRoleIntervals

open Common (Ty Subtype Equivalent)
open LayerBoundTemplates (Constraint Problem)

universe u

abbrev Interval (Bound : Type u) := Bound × Bound

def evaluate (eval : Bound → Ty) (interval : Interval Bound) : Interval Ty :=
  (eval interval.1, eval interval.2)

def Fits (interval : Interval Ty) (actual : Ty) : Prop :=
  Subtype interval.1 actual ∧ Subtype actual interval.2

def Valid (interval : Interval Ty) : Prop := Subtype interval.1 interval.2

def pin (type : Ty) : Interval Ty := (type, type)

def merge (first last : Interval Ty) : Interval Ty :=
  (.union first.1 last.1, .inter last.2 first.2)

theorem fits_merge (first last : Interval Ty) (actual : Ty) :
    Fits (merge first last) actual ↔ Fits first actual ∧ Fits last actual := by
  simp only [Fits, merge, Common.common_union_is_join, Common.common_inter_is_meet]
  exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, d⟩, ⟨b, c⟩⟩,
    fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨d, b⟩⟩⟩

theorem valid_iff_nonempty (interval : Interval Ty) :
    Valid interval ↔ ∃ actual, Fits interval actual := by
  constructor
  · intro valid
    exact ⟨interval.1, Common.subtype_refl _, valid⟩
  · rintro ⟨actual, lower, upper⟩
    exact Common.subtype_trans lower upper

/-- Both old consistency checks and both new cross checks are necessary. -/
theorem valid_merge_exact (first last : Interval Ty) :
    Valid (merge first last) ↔
      Valid first ∧ Valid last ∧ Subtype first.1 last.2 ∧ Subtype last.1 first.2 := by
  simp only [Valid, merge, Common.common_union_is_join, Common.common_inter_is_meet]
  exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨c, b, a, d⟩,
    fun ⟨a, b, c, d⟩ => ⟨⟨c, b⟩, ⟨a, d⟩⟩⟩

theorem fits_pin (type actual : Ty) : Fits (pin type) actual ↔ Equivalent actual type := by
  exact and_comm

theorem valid_pin (type : Ty) : Valid (pin type) := Common.subtype_refl type

/-- Endpoint equivalence is legitimate; existential point-head matching is
not used as the definition of reconciliation. -/
theorem fits_congr {first last : Interval Ty}
    (lower : Equivalent first.1 last.1) (upper : Equivalent first.2 last.2)
    (actual : Ty) : Fits first actual ↔ Fits last actual := by
  constructor
  · rintro ⟨lo, up⟩
    exact ⟨Common.subtype_trans lower.2 lo, Common.subtype_trans up upper.1⟩
  · rintro ⟨lo, up⟩
    exact ⟨Common.subtype_trans lower.1 lo, Common.subtype_trans up upper.2⟩

theorem merge_pin_valid (first last : Ty) :
    Valid (merge (pin first) (pin last)) ↔ Equivalent first last := by
  rw [valid_merge_exact]
  exact ⟨fun parts => ⟨parts.2.2.1, parts.2.2.2⟩,
    fun same => ⟨valid_pin _, valid_pin _, same.1, same.2⟩⟩

/-- This is the local variable-variable equality implication. It does not
delete a variable from any other principal-type occurrence. -/
theorem two_sided_equality (first last actual : Ty)
    (fits : Fits (merge (pin first) (pin last)) actual) : Equivalent first last :=
  (merge_pin_valid first last).mp ((valid_iff_nonempty _).mpr ⟨actual, fits⟩)

def coalesce (intervals : List (Interval Ty)) : Interval Ty :=
  (CommonBoundCoalescing.joinTypes (intervals.map Prod.fst),
    CommonBoundCoalescing.meetTypes (intervals.map Prod.snd))

theorem fits_coalesce (intervals : List (Interval Ty)) (actual : Ty) :
    Fits (coalesce intervals) actual ↔ ∀ interval ∈ intervals, Fits interval actual := by
  simp only [Fits, coalesce, CommonBoundCoalescing.joinTypes_le_iff,
    CommonBoundCoalescing.le_meetTypes_iff, List.forall_mem_map]
  exact ⟨fun ⟨lo, up⟩ interval present => ⟨lo interval present, up interval present⟩,
    fun all => ⟨fun interval present => (all interval present).1,
      fun interval present => (all interval present).2⟩⟩

theorem valid_coalesce (intervals : List (Interval Ty)) :
    Valid (coalesce intervals) ↔
      ∀ first ∈ intervals, ∀ last ∈ intervals, Subtype first.1 last.2 := by
  simp only [Valid, coalesce, CommonBoundCoalescing.joinTypes_le_iff,
    CommonBoundCoalescing.le_meetTypes_iff, List.forall_mem_map]
  exact ⟨fun all first present last included => all last included first present,
    fun all last included first present => all first present last included⟩

/-- Existing constraint syntax, no fresh central type slot. This produces
the old checks as well as both cross directions, in source-pair order. -/
def checks (intervals : List (Interval Bound)) : Problem n Bound :=
  intervals.flatMap fun first => intervals.map fun last => .check first.1 last.2

theorem mem_checks (intervals : List (Interval Bound)) (constraint : Constraint n Bound) :
    constraint ∈ checks intervals ↔
      ∃ first ∈ intervals, ∃ last ∈ intervals, constraint = .check first.1 last.2 := by
  simp only [checks, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨first, present, last, included, same⟩
    exact ⟨first, present, last, included, same.symm⟩
  · rintro ⟨first, present, last, included, same⟩
    exact ⟨first, present, last, included, same.symm⟩

theorem checks_exact (eval : Bound → Ty) (intervals : List (Interval Bound))
    (values : Fin n → Ty) :
    CommonBoundCoalescing.Models eval (checks intervals) values ↔
      ∀ first ∈ intervals, ∀ last ∈ intervals, Subtype (eval first.1) (eval last.2) := by
  constructor
  · intro model first present last included
    exact model (.check first.1 last.2)
      ((mem_checks intervals _).mpr ⟨first, present, last, included, rfl⟩)
  · intro all constraint present
    obtain ⟨first, member, last, included, rfl⟩ := (mem_checks intervals constraint).mp present
    exact all first member last included

theorem checks_valid_exact (eval : Bound → Ty) (intervals : List (Interval Bound))
    (values : Fin n → Ty) :
    CommonBoundCoalescing.Models eval (checks intervals) values ↔
      Valid (coalesce (intervals.map (evaluate eval))) := by
  rw [checks_exact, valid_coalesce]
  simp only [List.forall_mem_map, evaluate]

theorem checks_real_argument_exact (eval : Bound → Ty) (intervals : List (Interval Bound))
    (values : Fin n → Ty) :
    CommonBoundCoalescing.Models eval (checks intervals) values ↔
      ∃ actual, ∀ interval ∈ intervals, Fits (evaluate eval interval) actual := by
  rw [checks_valid_exact, valid_iff_nonempty]
  simp only [fits_coalesce, List.forall_mem_map]

theorem checks_length (intervals : List (Interval Bound)) :
    (checks (n := n) intervals).length = intervals.length * intervals.length := by
  simp only [checks, List.length_flatMap, List.length_map]
  have allLengths : ∀ rows : List (Interval Bound), ∀ count,
      (rows.map fun _ => count).sum = rows.length * count := by
    intro rows count
    induction rows with
    | nil => simp
    | cons _ rows ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
        exact Nat.add_comm _ _
  exact allLengths intervals intervals.length

theorem append_checks_exact (eval : Bound → Ty) (problem : Problem n Bound)
    (intervals : List (Interval Bound)) (values : Fin n → Ty) :
    CommonBoundCoalescing.Models eval (problem ++ checks intervals) values ↔
      CommonBoundCoalescing.Models eval problem values ∧
        Valid (coalesce (intervals.map (evaluate eval))) := by
  rw [← checks_valid_exact eval intervals values]
  simp only [CommonBoundCoalescing.Models, List.mem_append, or_imp, forall_and]

end Yulang.CommonRoleIntervals
