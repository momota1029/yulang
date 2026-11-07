import Yulang.CommonBoundCoalescing
import Yulang.CommonEffectFormula

/-!
Centre-less invariant argument bounds, as in spec 6.5 and the effect-family /
row-tail occurrence rule. An interval stores only its two endpoints. A member
below is an interpretation witness, never a stored centre or a dispatch key.

These lemmas describe interval merging and its complete parameter family.
They do not identify a family name with its invariant arguments, discharge
the endpoint comparisons, or implement nominal dispatch. In particular the
consistency tests are internal solver obligations, not parameter conditions.
-/
namespace Yulang.CommonEffectInvariantIntervals
open Common (Ty Row Subtype Equivalent rowLe)
open CommonBoundCoalescing

universe u
structure Interval (α : Type u) where
  lower : α
  upper : α

namespace Value
abbrev Bounds := Interval Ty

def Member (bounds : Bounds) (value : Ty) : Prop :=
  Subtype bounds.lower value ∧ Subtype value bounds.upper

def Consistent (bounds : Bounds) : Prop := Subtype bounds.lower bounds.upper

def merge (first last : Bounds) : Bounds :=
  ⟨.union first.lower last.lower, .inter first.upper last.upper⟩

def point (value : Ty) : Bounds := ⟨value, value⟩

def instantiate (bounds : Bounds) (parameter : Ty) : Ty :=
  .union bounds.lower (.inter parameter bounds.upper)

theorem merge_member (first last : Bounds) (value : Ty) :
    Member (merge first last) value ↔ Member first value ∧ Member last value := by
  simp only [Member, merge, Common.common_union_is_join, Common.common_inter_is_meet]
  exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩,
    fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩

theorem merge_consistent (first last : Bounds) :
    Consistent (merge first last) ↔ Consistent first ∧ Consistent last ∧
      Subtype first.lower last.upper ∧ Subtype last.lower first.upper := by
  simp only [Consistent, merge, Common.common_union_is_join, Common.common_inter_is_meet]
  exact ⟨fun h => ⟨h.1.1, h.2.2, h.2.1, h.1.2⟩,
    fun h => ⟨⟨h.1, h.2.2.2⟩, h.2.2.1, h.2.1⟩⟩

theorem consistent_iff_member (bounds : Bounds) :
    Consistent bounds ↔ ∃ value, Member bounds value := by
  constructor
  · intro checked
    exact ⟨bounds.lower, Common.subtype_refl _, checked⟩
  · rintro ⟨value, lower, upper⟩
    exact Common.subtype_trans lower upper

theorem point_member (value actual : Ty) :
    Member (point value) actual ↔ Equivalent value actual := Iff.rfl

theorem instantiate_member (bounds : Bounds) (checked : Consistent bounds) (parameter : Ty) :
    Member bounds (instantiate bounds parameter) := by
  constructor
  · exact le_union_left _ _
  · exact (Common.common_union_is_join _ _ _).mpr
      ⟨checked, inter_le_right _ _⟩

theorem instantiate_retraction (bounds : Bounds) (value : Ty) (member : Member bounds value) :
    Equivalent (instantiate bounds value) value := by
  constructor
  · apply (Common.common_union_is_join _ _ _).mpr
    exact ⟨member.1, inter_le_left _ _⟩
  · apply Common.subtype_trans (middle := .inter value bounds.upper)
    · exact (Common.common_inter_is_meet _ _ _).mpr ⟨Common.subtype_refl _, member.2⟩
    · exact le_union_right _ _

/-- All parameters are unrestricted. No membership predicate is imposed on a
parameter; the two endpoints are checked once, before this family is used. -/
theorem all_instances_exact (bounds : Bounds) (checked : Consistent bounds) (value : Ty) :
    Member bounds value ↔ ∃ parameter, Equivalent (instantiate bounds parameter) value := by
  constructor
  · intro member
    exact ⟨value, instantiate_retraction bounds value member⟩
  · rintro ⟨parameter, same⟩
    have member := instantiate_member bounds checked parameter
    exact ⟨Common.subtype_trans member.1 same.1, Common.subtype_trans same.2 member.2⟩

end Value

namespace EffectRow
abbrev Bounds := Interval Row

def meet (first last : Row) : Row := fun occurrence => first occurrence ∧ last occurrence

def Member (bounds : Bounds) (row : Row) : Prop :=
  rowLe bounds.lower row ∧ rowLe row bounds.upper

def Consistent (bounds : Bounds) : Prop := rowLe bounds.lower bounds.upper

def merge (first last : Bounds) : Bounds :=
  ⟨Common.rowJoin first.lower last.lower, meet first.upper last.upper⟩

def point (row : Row) : Bounds := ⟨row, row⟩

def instantiate (bounds : Bounds) (parameter : Row) : Row :=
  Common.rowJoin bounds.lower (meet parameter bounds.upper)

theorem merge_member (first last : Bounds) (row : Row) :
    Member (merge first last) row ↔ Member first row ∧ Member last row := by
  constructor
  · rintro ⟨lower, upper⟩
    exact ⟨⟨fun occurrence member => lower occurrence (Or.inl member),
      fun occurrence member => (upper occurrence member).1⟩,
      ⟨fun occurrence member => lower occurrence (Or.inr member),
      fun occurrence member => (upper occurrence member).2⟩⟩
  · rintro ⟨⟨loFirst, upFirst⟩, ⟨loLast, upLast⟩⟩
    exact ⟨fun occurrence member => member.elim (loFirst occurrence) (loLast occurrence),
      fun occurrence member => ⟨upFirst occurrence member, upLast occurrence member⟩⟩

theorem merge_consistent (first last : Bounds) :
    Consistent (merge first last) ↔ Consistent first ∧ Consistent last ∧
      rowLe first.lower last.upper ∧ rowLe last.lower first.upper := by
  constructor
  · intro checked
    exact ⟨fun occurrence member => (checked occurrence (Or.inl member)).1,
      fun occurrence member => (checked occurrence (Or.inr member)).2,
      fun occurrence member => (checked occurrence (Or.inl member)).2,
      fun occurrence member => (checked occurrence (Or.inr member)).1⟩
  · rintro ⟨firstChecked, lastChecked, crossFirst, crossLast⟩ occurrence member
    exact member.elim
      (fun member => ⟨firstChecked occurrence member, crossFirst occurrence member⟩)
      (fun member => ⟨crossLast occurrence member, lastChecked occurrence member⟩)

theorem consistent_iff_member (bounds : Bounds) :
    Consistent bounds ↔ ∃ row, Member bounds row := by
  constructor
  · intro checked
    exact ⟨bounds.lower, fun _ => id, checked⟩
  · rintro ⟨row, lower, upper⟩ occurrence member
    exact upper occurrence (lower occurrence member)

theorem point_member (row actual : Row) : Member (point row) actual ↔ row = actual := by
  constructor
  · intro member
    funext occurrence
    exact propext ⟨member.1 occurrence, member.2 occurrence⟩
  · rintro rfl
    exact ⟨fun _ => id, fun _ => id⟩

theorem instantiate_member (bounds : Bounds) (checked : Consistent bounds) (parameter : Row) :
    Member bounds (instantiate bounds parameter) := by
  exact ⟨fun _ => Or.inl,
    fun occurrence member => member.elim (checked occurrence) And.right⟩

theorem instantiate_retraction (bounds : Bounds) (row : Row) (member : Member bounds row) :
    instantiate bounds row = row := by
  funext occurrence
  apply propext
  exact ⟨fun present => present.elim (member.1 occurrence) And.left,
    fun present => Or.inr ⟨present, member.2 occurrence present⟩⟩

theorem all_instances_exact (bounds : Bounds) (checked : Consistent bounds) (row : Row) :
    Member bounds row ↔ ∃ parameter, instantiate bounds parameter = row := by
  constructor
  · intro member
    exact ⟨row, instantiate_retraction bounds row member⟩
  · rintro ⟨parameter, rfl⟩
    exact instantiate_member bounds checked parameter

end EffectRow

open Core.PresenceGeneration

/-- Finite value syntax for both endpoints; no central type variable is
silently added. Family identity and argument kind checking are separate. -/
abbrev ValueTerms (α : Type) := Interval (TyTerm α)

def ValueTerms.eval (bounds : ValueTerms α) (assignment : α → CommonEffectRequestGeneration.Computation) :
    Value.Bounds :=
  ⟨bounds.lower.eval Common.model assignment, bounds.upper.eval Common.model assignment⟩

def ValueTerms.check (bounds : ValueTerms α) : CommonEffectFormula.Formula scopes α :=
  .core (.tyLe bounds.lower bounds.upper)

theorem ValueTerms.check_exact (bounds : ValueTerms α)
    (assignment : α → CommonEffectRequestGeneration.Computation) :
    (bounds.check (scopes := scopes)).Holds assignment ↔ Value.Consistent (bounds.eval assignment) :=
  Iff.rfl

def ValueTerms.merge (first last : ValueTerms α) : ValueTerms α :=
  ⟨.union first.lower last.lower, .inter first.upper last.upper⟩

theorem ValueTerms.eval_merge (first last : ValueTerms α)
    (assignment : α → CommonEffectRequestGeneration.Computation) :
    (first.merge last).eval assignment = Value.merge (first.eval assignment) (last.eval assignment) := rfl

/-- Real, finite endpoint comparisons, including both cross constraints. -/
theorem ValueTerms.merge_check_exact (first last : ValueTerms α)
    (assignment : α → CommonEffectRequestGeneration.Computation) :
    ((first.merge last).check (scopes := scopes)).Holds assignment ↔
      (CommonEffectFormula.Formula.and (first.check (scopes := scopes))
        (.and last.check (.and (.core (.tyLe first.lower last.upper))
          (.core (.tyLe last.lower first.upper))))).Holds assignment := by
  exact Value.merge_consistent (first.eval assignment) (last.eval assignment)

end Yulang.CommonEffectInvariantIntervals
