import Yulang.ProducerContextual
import Yulang.ValueBoundSchemes

/-!
# Retraction of actual value-bound schemes in the contextual order

The problem, reachability algorithm, lower/upper bound expressions and shared
parameter expansion are exactly those of `ValueBounds` / `ValueBoundSchemes`.
Only the independent interpretation of each inequality changes. All bounds and
parameters are arbitrary finite contextual types, including arrows and rows.

The key theorem `expand_equivalent` proves that substituting any independent
contextual solution for the parameters recovers that solution. Structural
subtyping of that original solution is never assumed. This is the finite-layer
surjectivity lemma needed by regular coalescing at every observation depth.
-/

namespace Yulang.ContextualValueBounds

open StructuralBase
open ValueBounds (Constraint Problem Valuation Reaches joinTypes least)
open ValueUpperBounds (meetTypes greatest)
open ValueBoundSchemes (variablePart expand)
open ProducerContextual

universe u
variable {n : Nat} {Row : Type u} {leRow : Row → Row → Prop}

def ConstraintHolds (leRow : Row → Row → Prop) (value : Valuation n Row) : Constraint n Row → Prop
  | .lower type target => ProducerLe leRow type (value target)
  | .flow source target => ProducerLe leRow (value source) (value target)
  | .upper source type => ProducerLe leRow (value source) type
  | .check source target => ProducerLe leRow source target

def Models (leRow : Row → Row → Prop) (problem : Problem n Row) (value : Valuation n Row) : Prop :=
  ∀ constraint ∈ problem, ConstraintHolds leRow value constraint

theorem bottom_le (type : Ty Row) : ProducerLe leRow .bottom type := by
  apply (producerLe_iff_probe _ _).mpr
  exact fun rank _ obs _ => probeAt_bottom rank obs

theorem le_top (type : Ty Row) : ProducerLe leRow type .top := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep]

theorem inter_le_left (first last : Ty Row) : ProducerLe leRow (.inter first last) first := by
  apply (producerLe_iff_probe _ _).mpr
  exact fun rank _ obs accepted => (probeAt_inter rank first last obs).mpr (Or.inl accepted)

theorem inter_le_right (first last : Ty Row) : ProducerLe leRow (.inter first last) last := by
  apply (producerLe_iff_probe _ _).mpr
  exact fun rank _ obs accepted => (probeAt_inter rank first last obs).mpr (Or.inr accepted)

theorem joinTypes_le_iff (types : List (Ty Row)) (upper : Ty Row) :
    ProducerLe leRow (joinTypes types) upper ↔ ∀ type ∈ types, ProducerLe leRow type upper := by
  induction types with
  | nil => simp only [joinTypes, List.not_mem_nil, false_implies, implies_true]; exact iff_true_intro (bottom_le upper)
  | cons type rest ih =>
      simp only [joinTypes, producerLe_union_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem le_meetTypes_iff (lower : Ty Row) (types : List (Ty Row)) :
    ProducerLe leRow lower (meetTypes types) ↔ ∀ type ∈ types, ProducerLe leRow lower type := by
  induction types with
  | nil => simp only [meetTypes, List.not_mem_nil, false_implies, implies_true]; exact iff_true_intro (le_top lower)
  | cons type rest ih =>
      simp only [meetTypes, producerLe_inter_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem reaches_le {problem : Problem n Row} {value : Valuation n Row}
    (model : Models leRow problem value) {source target : Fin n} (path : Reaches problem source target) :
    ProducerLe leRow (value source) (value target) := by
  induction path with
  | nil => exact producerLe_refl _
  | @cons source middle target edge rest ih =>
      exact producerLe_trans (model (.flow source middle)
        ((ValueBounds.mem_successors problem source middle).mp edge)) ih

theorem least_below {problem : Problem n Row} {value : Valuation n Row}
    (model : Models leRow problem value) (target : Fin n) :
    ProducerLe leRow (least problem target) (value target) := by
  apply (joinTypes_le_iff _ _).mpr
  intro type contributes
  obtain ⟨source, seed, path⟩ := (ValueBounds.mem_lowerTypes problem target type).mp contributes
  exact producerLe_trans (model (.lower type source) seed) (reaches_le model path)

theorem greatest_above {problem : Problem n Row} {value : Valuation n Row}
    (model : Models leRow problem value) (source : Fin n) :
    ProducerLe leRow (value source) (greatest problem source) := by
  apply (le_meetTypes_iff _ _).mpr
  intro type contributes
  obtain ⟨target, bound, path⟩ := (ValueUpperBounds.mem_upperTypes problem source type).mp contributes
  exact producerLe_trans (reaches_le model path) (model (.upper target type) bound)

theorem variablePart_le_iff (problem : Problem n Row) (parameters : Valuation n Row)
    (target : Fin n) (upper : Ty Row) :
    ProducerLe leRow (variablePart problem parameters target) upper ↔
      ∀ source, Reaches problem source target →
        ProducerLe leRow (.inter (parameters source) (greatest problem source)) upper := by
  simp only [variablePart, joinTypes_le_iff, List.forall_mem_map, ValueBoundSchemes.mem_ancestors]

theorem contribution_below (problem : Problem n Row) (parameters : Valuation n Row)
    (source target : Fin n) (path : Reaches problem source target) :
    ProducerLe leRow (.inter (parameters source) (greatest problem source))
      (variablePart problem parameters target) :=
  (variablePart_le_iff problem parameters target _).mp (producerLe_refl _) source path

/-- All independent contextual solutions are recovered by the existing
shared-parameter expansion; no structural solution premise or row law is used. -/
theorem expand_equivalent {problem : Problem n Row} {value : Valuation n Row}
    (model : Models leRow problem value) (target : Fin n) :
    ProducerEq leRow (expand problem value target) (value target) := by
  constructor
  · apply (producerLe_union_iff _ _ _).mpr
    refine ⟨least_below model target, ?_⟩
    apply (variablePart_le_iff problem value target _).mpr
    intro source path
    exact producerLe_trans (inter_le_left _ _) (reaches_le model path)
  · exact producerLe_trans
      ((producerLe_inter_iff _ _ _).mpr ⟨producerLe_refl _, greatest_above model target⟩)
      (producerLe_trans (contribution_below problem value target target (.nil target))
        (producerLe_union_right _ _))

end Yulang.ContextualValueBounds
