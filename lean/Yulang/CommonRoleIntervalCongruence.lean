import Yulang.CommonRoleIntervalGeneration

/-!
# Globally sound variable equality after interval constraints

Equality forced by both sides of an interval permits identification in every
ordinary constraint, including negative arrow positions and record defaults.
Rows are preserved literally. The deterministic identification below changes
the type component only; it never chooses an interval's actual-type center.
This is the variable-variable implication, not the whole-type concrete
sandwich algorithm or its level-sensitive scheduling.
-/

namespace Yulang.CommonRoleIntervalCongruence

open Core.PresenceGeneration (TyTerm RowTerm Comp Formula extend)
open Common (Equivalent Subtype)
open CommonRoleIntervals (pin merge Valid)

def Related (first last : α → Comp Common.model) : Prop :=
  ∀ name, Equivalent (first name).1 (last name).1 ∧ (first name).2 = (last name).2

theorem related_refl (assignment : α → Comp Common.model) : Related assignment assignment :=
  fun _ => ⟨Common.equivalent_refl _, rfl⟩

theorem related_symm {first last : α → Comp Common.model} (same : Related first last) :
    Related last first := fun name => ⟨Common.equivalent_symm (same name).1, (same name).2.symm⟩

theorem related_extend {first last : α → Comp Common.model} (same : Related first last)
    (value : Comp Common.model) : Related (extend first value) (extend last value) := by
  intro name
  cases name with
  | none => exact ⟨Common.equivalent_refl _, rfl⟩
  | some name => exact same name

theorem row_eval_equal {first last : α → Comp Common.model} (same : Related first last)
    (term : RowTerm α) : term.eval Common.model first = term.eval Common.model last := by
  induction term with
  | var name => exact (same name).2
  | empty => rfl
  | join _ _ ihFirst ihLast => simp only [RowTerm.eval, ihFirst, ihLast]

theorem type_eval_equivalent {first last : α → Comp Common.model} (same : Related first last)
    (term : TyTerm α) : Equivalent (term.eval Common.model first) (term.eval Common.model last) := by
  induction term with
  | var name => exact (same name).1
  | base | bottom | top | emptyRecord | exactEmpty => exact Common.equivalent_refl _
  | union _ _ ihFirst ihLast =>
      exact ⟨Common.common_union_mono ihFirst.1 ihLast.1,
        Common.common_union_mono ihFirst.2 ihLast.2⟩
  | inter _ _ ihFirst ihLast =>
      exact ⟨Common.common_inter_mono ihFirst.1 ihLast.1,
        Common.common_inter_mono ihFirst.2 ihLast.2⟩
  | pair _ _ ihFirst ihLast =>
      exact ⟨(Common.common_pair_iff _ _ _ _).mpr ⟨ihFirst.1, ihLast.1⟩,
        (Common.common_pair_iff _ _ _ _).mpr ⟨ihFirst.2, ihLast.2⟩⟩
  | required label _ ih =>
      exact ⟨Common.common_record_mono label ih.1 (Common.subtype_refl _),
        Common.common_record_mono label ih.2 (Common.subtype_refl _)⟩
  | record label _ _ ihPayload ihTail =>
      exact ⟨Common.common_record_mono label ihPayload.1 ihTail.1,
        Common.common_record_mono label ihPayload.2 ihTail.2⟩
  | recordDefault label _ _ ihSource ihFallback =>
      exact Common.common_default_congr label ihSource ihFallback
  | variant label _ ih =>
      exact ⟨(Common.common_variant_iff label _ _).mpr ih.1,
        (Common.common_variant_iff label _ _).mpr ih.2⟩
  | arrow input incoming output outgoing ihInput ihOutput =>
      simp only [TyTerm.eval, row_eval_equal same incoming, row_eval_equal same outgoing]
      exact ⟨(Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
          ⟨ihInput.2, Common.rowLe_refl _, ihOutput.1, Common.rowLe_refl _⟩,
        (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
          ⟨ihInput.1, Common.rowLe_refl _, ihOutput.2, Common.rowLe_refl _⟩⟩

theorem subtype_congr {a b c d : Common.Ty} (first : Equivalent a b) (last : Equivalent c d) :
    Subtype a c ↔ Subtype b d :=
  ⟨fun below => Common.subtype_trans first.2 (Common.subtype_trans below last.1),
    fun below => Common.subtype_trans first.1 (Common.subtype_trans below last.2)⟩

theorem atom_holds_congr {first last : α → Comp Common.model} (same : Related first last)
    (atom : PresenceNormalForm.Atom α) :
    atom.Holds Common.model first ↔ atom.Holds Common.model last := by
  cases atom with
  | tyLe source target =>
      exact subtype_congr (type_eval_equivalent same source) (type_eval_equivalent same target)
  | rowLe source target =>
      simp only [PresenceNormalForm.Atom.Holds, row_eval_equal same source, row_eval_equal same target]

theorem all_holds_congr {first last : α → Comp Common.model} (same : Related first last)
    (atoms : List (PresenceNormalForm.Atom α)) :
    PresenceNormalForm.All Common.model first atoms ↔ PresenceNormalForm.All Common.model last atoms := by
  exact forall_congr' fun atom => imp_congr_right fun _ => atom_holds_congr same atom

/-- The quantifier binds the same fresh computation on both sides. Ambient
sharing is preserved rather than independently re-generalized. -/
theorem formula_holds_congr (formula : Formula α) {first last : α → Comp Common.model}
    (same : Related first last) :
    formula.Holds Common.model first ↔ formula.Holds Common.model last := by
  induction formula with
  | top | bot => rfl
  | and _ _ ihFirst ihLast => exact and_congr (ihFirst same) (ihLast same)
  | or _ _ ihFirst ihLast => exact or_congr (ihFirst same) (ihLast same)
  | tyLe source target =>
      exact subtype_congr (type_eval_equivalent same source) (type_eval_equivalent same target)
  | rowLe source target =>
      simp only [Formula.Holds, row_eval_equal same source, row_eval_equal same target]
  | existsSlot formula ih =>
      exact exists_congr fun value => ih (related_extend same value)

def identify [DecidableEq α] (representative removed : α) (assignment : α → Comp Common.model) :
    α → Comp Common.model := fun name =>
  (if name = removed then (assignment representative).1 else (assignment name).1,
    (assignment name).2)

theorem identify_related [DecidableEq α] (representative removed : α)
    (assignment : α → Comp Common.model)
    (forced : Valid (merge (pin (assignment representative).1) (pin (assignment removed).1))) :
    Related assignment (identify representative removed assignment) := by
  have equal := (CommonRoleIntervals.merge_pin_valid _ _).mp forced
  intro name
  by_cases replaced : name = removed
  · subst name
    exact ⟨by simpa [identify] using Common.equivalent_symm equal, rfl⟩
  · exact ⟨by simpa [identify, replaced] using Common.equivalent_refl (assignment name).1, rfl⟩

theorem identified_equal [DecidableEq α] (representative removed : α)
    (assignment : α → Comp Common.model) :
    (identify representative removed assignment representative).1 =
      (identify representative removed assignment removed).1 := by
  by_cases same : representative = removed
  · subst removed; rfl
  · simp [identify, same]

theorem global_formula_identification [DecidableEq α] (representative removed : α)
    (assignment : α → Comp Common.model) (formula : Formula α)
    (forced : Valid (merge (pin (assignment representative).1) (pin (assignment removed).1))) :
    formula.Holds Common.model assignment ↔
      formula.Holds Common.model (identify representative removed assignment) :=
  formula_holds_congr formula (identify_related representative removed assignment forced)

theorem global_atoms_identification [DecidableEq α] (representative removed : α)
    (assignment : α → Comp Common.model) (atoms : List (PresenceNormalForm.Atom α))
    (forced : Valid (merge (pin (assignment representative).1) (pin (assignment removed).1))) :
    PresenceNormalForm.All Common.model assignment atoms ↔
      PresenceNormalForm.All Common.model (identify representative removed assignment) atoms :=
  all_holds_congr (identify_related representative removed assignment forced) atoms

theorem interval_checks_identification [DecidableEq α] (representative removed : α)
    (assignment : α → Comp Common.model)
    (arguments : List (CommonRoleIntervalGeneration.Argument α))
    (forced : Valid (merge (pin (assignment representative).1) (pin (assignment removed).1))) :
    Valid (CommonRoleIntervalGeneration.meaning assignment arguments) ↔
      Valid (CommonRoleIntervalGeneration.meaning
        (identify representative removed assignment) arguments) := by
  rw [← CommonRoleIntervalGeneration.generate_exact,
    ← CommonRoleIntervalGeneration.generate_exact]
  exact global_atoms_identification representative removed assignment _ forced

/-- The equality premise is here obtained from the actual generated
ordinary atoms, not assumed to be a discovery of the co-occurrence pass. -/
theorem generated_variables_equal (first last : α) (assignment : α → Comp Common.model)
    (held : PresenceNormalForm.All Common.model assignment
      (CommonRoleIntervalGeneration.generate [(.var first, .var first), (.var last, .var last)])) :
    Equivalent (assignment first).1 (assignment last).1 := by
  have valid := (CommonRoleIntervalGeneration.generate_exact assignment _).mp held
  change Valid (CommonRoleIntervals.coalesce
    [pin (assignment first).1, pin (assignment last).1]) at valid
  have comparisons := (CommonRoleIntervals.valid_coalesce _).mp valid
  exact ⟨comparisons (pin (assignment first).1) (by simp)
      (pin (assignment last).1) (by simp),
    comparisons (pin (assignment last).1) (by simp) (pin (assignment first).1) (by simp)⟩

theorem global_formula_from_generated [DecidableEq α] (representative removed : α)
    (assignment : α → Comp Common.model) (formula : Formula α)
    (held : PresenceNormalForm.All Common.model assignment
      (CommonRoleIntervalGeneration.generate
        [(.var representative, .var representative), (.var removed, .var removed)])) :
    formula.Holds Common.model assignment ↔
      formula.Holds Common.model (identify representative removed assignment) :=
  global_formula_identification representative removed assignment formula
    ((CommonRoleIntervals.merge_pin_valid _ _).mpr
      (generated_variables_equal representative removed assignment held))

end Yulang.CommonRoleIntervalCongruence
