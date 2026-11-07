import Yulang.CommonNominalTemplateCongruence
import Yulang.CommonNominalFieldNormalForm

/-!
# Original generated constraints respect recovered full-carrier assignments

Every ambient type is recovered modulo demand equivalence, every row is
recovered literally, and every occurrence uses that same assignment. Ordinary
terms, full field templates, generated formulas and packed atomic constraints
all preserve their independent meaning. No solver or source typing is an
assumption of these congruence theorems.
-/

namespace Yulang.CommonNominalConstraintCongruence

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm extend)

def AssignmentEquivalent (first last : α → Comp model) : Prop :=
  ∀ index, Equivalent (first index).1 (last index).1 ∧ (first index).2 = (last index).2

theorem row_eval (first last : α → Comp model) (same : AssignmentEquivalent first last) (term : RowTerm α) :
    term.eval model first = term.eval model last := by
  induction term with
  | var index => exact (same index).2
  | empty => rfl
  | join first last ihFirst ihLast => simp only [RowTerm.eval, ihFirst, ihLast]

private theorem union_equiv {a b c d : Ty} (first : Equivalent a b) (last : Equivalent c d) :
    Equivalent (.union a c) (.union b d) :=
  ⟨common_union_mono first.1 last.1, common_union_mono first.2 last.2⟩

private theorem inter_equiv {a b c d : Ty} (first : Equivalent a b) (last : Equivalent c d) :
    Equivalent (.inter a c) (.inter b d) :=
  ⟨common_inter_mono first.1 last.1, common_inter_mono first.2 last.2⟩

private theorem record_equiv (label : Nat) {a b c d : Ty} (first : Equivalent a b) (last : Equivalent c d) :
    Equivalent (record label a c) (record label b d) :=
  ⟨common_record_mono label first.1 last.1, common_record_mono label first.2 last.2⟩

theorem type_eval (first last : α → Comp model) (same : AssignmentEquivalent first last) (term : TyTerm α) :
    Equivalent (term.eval model first) (term.eval model last) := by
  induction term with
  | var index => exact (same index).1
  | base | bottom | top | emptyRecord | exactEmpty => exact equivalent_refl _
  | union _ _ ihFirst ihLast => exact union_equiv ihFirst ihLast
  | inter _ _ ihFirst ihLast => exact inter_equiv ihFirst ihLast
  | pair _ _ ihFirst ihLast =>
      exact ⟨(common_pair_iff _ _ _ _).mpr ⟨ihFirst.1, ihLast.1⟩,
        (common_pair_iff _ _ _ _).mpr ⟨ihFirst.2, ihLast.2⟩⟩
  | required label _ ih => exact record_equiv label ih (equivalent_refl _)
  | record label _ _ ihFirst ihLast => exact record_equiv label ihFirst ihLast
  | recordDefault label _ _ ihFirst ihLast => exact common_default_congr label ihFirst ihLast
  | variant label _ ih =>
      exact ⟨(common_variant_iff label _ _).mpr ih.1, (common_variant_iff label _ _).mpr ih.2⟩
  | arrow input incoming output outgoing ihInput ihOutput =>
      change Equivalent
        (arrow (input.eval model first) (incoming.eval model first) (output.eval model first) (outgoing.eval model first))
        (arrow (input.eval model last) (incoming.eval model last) (output.eval model last) (outgoing.eval model last))
      rw [row_eval first last same incoming, row_eval first last same outgoing]
      exact ⟨(common_arrow_iff _ _ _ _ _ _ _ _).mpr
          ⟨ihInput.2, Common.rowLe_refl _, ihOutput.1, Common.rowLe_refl _⟩,
        (common_arrow_iff _ _ _ _ _ _ _ _).mpr
          ⟨ihInput.1, Common.rowLe_refl _, ihOutput.2, Common.rowLe_refl _⟩⟩

theorem subtype_congr {first first' last last' : Ty} (before : Equivalent first first') (after : Equivalent last last') :
    Subtype first last ↔ Subtype first' last' :=
  ⟨fun below => subtype_trans before.2 (subtype_trans below after.1),
    fun below => subtype_trans before.1 (subtype_trans below after.2)⟩

theorem term_eval (first last : α → Comp model) (same : AssignmentEquivalent first last)
    (term : CommonNominalFieldTemplates.Term α) : Equivalent (term.eval first) (term.eval last) := by
  cases term with
  | ordinary term => exact type_eval first last same term
  | template template arguments rows =>
      have rowsSame : (fun index => (rows index).eval model first) = (fun index => (rows index).eval model last) :=
        funext fun index => row_eval first last same (rows index)
      simp only [CommonNominalFieldTemplates.Term.eval, rowsSame]
      exact CommonNominalTemplateCongruence.template_eval_congr _ _ _ _
        (fun index => type_eval first last same (arguments index))

theorem extend_same (first last : α → Comp model) (same : AssignmentEquivalent first last) (fresh : Comp model) :
    AssignmentEquivalent (extend first fresh) (extend last fresh) := by
  intro index
  cases index with
  | none => exact ⟨equivalent_refl _, rfl⟩
  | some index => exact same index

theorem ordinary_formula_congr (formula : Core.PresenceGeneration.Formula α)
    (first last : α → Comp model) (same : AssignmentEquivalent first last) :
    formula.Holds model first ↔ formula.Holds model last := by
  induction formula with
  | top | bot => rfl
  | and _ _ ihFirst ihLast => exact and_congr (ihFirst first last same) (ihLast first last same)
  | or _ _ ihFirst ihLast => exact or_congr (ihFirst first last same) (ihLast first last same)
  | tyLe before after => exact subtype_congr (type_eval first last same before) (type_eval first last same after)
  | rowLe before after =>
      simp only [Core.PresenceGeneration.Formula.Holds, row_eval first last same before, row_eval first last same after]
  | existsSlot body ih =>
      apply exists_congr
      intro fresh
      exact ih (extend first fresh) (extend last fresh) (extend_same first last same fresh)

theorem formula_congr (formula : CommonNominalFieldTemplates.Formula α)
    (first last : α → Comp model) (same : AssignmentEquivalent first last) :
    formula.Models first ↔ formula.Models last := by
  induction formula with
  | ordinary formula => exact ordinary_formula_congr formula first last same
  | tyLe before after => exact subtype_congr (term_eval first last same before) (term_eval first last same after)
  | and _ _ ihFirst ihLast => exact and_congr (ihFirst first last same) (ihLast first last same)
  | or _ _ ihFirst ihLast => exact or_congr (ihFirst first last same) (ihLast first last same)
  | existsSlot body ih =>
      apply exists_congr
      intro fresh
      exact ih (extend first fresh) (extend last fresh) (extend_same first last same fresh)

theorem atom_congr (atom : CommonNominalFieldNormalForm.Atom α)
    (first last : α → Comp model) (same : AssignmentEquivalent first last) :
    atom.Models first ↔ atom.Models last := by
  cases atom with
  | tyLe before after => exact subtype_congr (term_eval first last same before) (term_eval first last same after)
  | rowLe before after => simp only [CommonNominalFieldNormalForm.Atom.Models,
      row_eval first last same before, row_eval first last same after]

theorem all_atoms_congr (atoms : List (CommonNominalFieldNormalForm.Atom α))
    (first last : α → Comp model) (same : AssignmentEquivalent first last) :
    CommonNominalFieldNormalForm.All first atoms ↔ CommonNominalFieldNormalForm.All last atoms := by
  constructor <;> intro model atom member
  · exact (atom_congr atom first last same).mp (model atom member)
  · exact (atom_congr atom first last same).mpr (model atom member)

end Yulang.CommonNominalConstraintCongruence
