import Yulang.CommonPatternFiniteSchemes
import Yulang.CommonCanonicalShapes

/-! Finite formulas respect demand equivalence of every free value and
literal equality of every free row, including negative arrow children. -/

namespace Yulang.CommonPatternFormulaEquivalence

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open Common (Equivalent)

def AssignmentEquivalent (first last : α → Comp Common.model) : Prop :=
  ∀ index, Equivalent (first index).1 (last index).1 ∧ (first index).2 = (last index).2

variable {first last : α → Comp Common.model}

theorem row_eval (same : AssignmentEquivalent first last) (term : RowTerm α) :
    term.eval Common.model first = term.eval Common.model last := by
  induction term with
  | var index => exact (same index).2
  | empty => rfl
  | join first last ihf ihl => simp only [RowTerm.eval, ihf, ihl]

theorem type_eval (same : AssignmentEquivalent first last) (term : TyTerm α) :
    Equivalent (term.eval Common.model first) (term.eval Common.model last) := by
  induction term with
  | var index => exact (same index).1
  | base | bottom | top | emptyRecord | exactEmpty => exact Common.equivalent_refl _
  | union first last ihf ihl => exact ⟨Common.common_union_mono ihf.1 ihl.1, Common.common_union_mono ihf.2 ihl.2⟩
  | inter first last ihf ihl => exact ⟨Common.common_inter_mono ihf.1 ihl.1, Common.common_inter_mono ihf.2 ihl.2⟩
  | pair first last ihf ihl => exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨ihf, ihl⟩
  | required label payload ih => exact (CommonCanonicalShapes.required_equivalent_iff label _ _).mpr ih
  | record label head tail ihh iht =>
      exact ⟨Common.common_record_mono label ihh.1 iht.1, Common.common_record_mono label ihh.2 iht.2⟩
  | recordDefault label source fallback ihs ihf => exact Common.common_default_congr label ihs ihf
  | variant tag payload ih => exact (CommonCanonicalShapes.variant_equivalent_iff tag _ _).mpr ih
  | arrow input incoming output outgoing ihi iho =>
      simp only [TyTerm.eval, row_eval same incoming, row_eval same outgoing]
      exact (CommonCanonicalShapes.arrow_equivalent_iff _ _ _ _ _ _).mpr ⟨ihi, iho⟩

theorem extend_same (same : AssignmentEquivalent first last) (value : Comp Common.model) :
    AssignmentEquivalent (extend first value) (extend last value) := by
  intro index
  cases index with
  | none => exact ⟨Common.equivalent_refl _, rfl⟩
  | some index => exact same index

/-- Arbitrary formula syntax and arbitrary equivalent assignments; no finite
source grammar, model witness or successful solve is assumed. -/
theorem holds_exact (formula : Formula α) (same : AssignmentEquivalent first last) :
    formula.Holds Common.model first ↔ formula.Holds Common.model last := by
  induction formula with
  | top | bot => rfl
  | tyLe source target =>
      exact CommonSymbolicBoundInspection.subtype_congr (type_eval same source) (type_eval same target)
  | rowLe source target => simp only [Formula.Holds, row_eval same source, row_eval same target]
  | and left right ihl ihr => exact and_congr (ihl same) (ihr same)
  | or left right ihl ihr => exact or_congr (ihl same) (ihr same)
  | existsSlot formula ih =>
      simp only [Formula.Holds]
      exact exists_congr (fun value => ih (extend_same same value))

end Yulang.CommonPatternFormulaEquivalence

namespace Yulang.CommonPatternFiniteSchemes

open Core.PresenceGeneration
open CommonPatternGenerationProvenance (SafeFormula)
open CommonPatternFormulaEquivalence (AssignmentEquivalent)

/-- The actual finite solved list represents exactly all free-slot models,
up to demand equivalence, with every row literal. Parameters are unrestricted.
Source provenance must supply SafeFormula; this is an internal solver lemma. -/
theorem formula_instances_exact (formula : Formula (Fin n)) (good : SafeFormula formula)
    (assignment : Fin n → Comp Common.model) :
    formula.Holds Common.model assignment ↔
      ∃ scheme ∈ infer formula, ∃ parameters : scheme.Parameters,
        AssignmentEquivalent (scheme.instantiate parameters) assignment := by
  constructor
  · exact parameter_retraction formula good assignment
  · rintro ⟨scheme, returned, parameters, same⟩
    exact (CommonPatternFormulaEquivalence.holds_exact formula same).mp
      (all_parameter_holds formula scheme returned parameters)

end Yulang.CommonPatternFiniteSchemes
