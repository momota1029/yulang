import Yulang.CommonLegacyRegularErasure
import Yulang.CommonLegacyEmbeddedWitnesses
import Yulang.CoreCommonInference

/-! Recovery of shared old witnesses from arbitrary Common source typings. -/

namespace Yulang.CommonLegacySharedWitnesses

open Core.PresenceGeneration
open CommonLegacyEmptyReflection (legacyModel contextualModel)
open CommonLegacyRegularErasure (eraseType eraseType_observe eraseType_mono)
open CommonLegacyGenerationTranslation (translateType translateFormula)
open CommonLegacyGeneratedAtoms (eraseRow)
open CommonLegacyGeneratedErasure (clean CleanFormula)

noncomputable def eraseComp (value : Comp Common.model) : Inference.Comp contextualModel :=
  (eraseType value.1, value.2)

noncomputable def eraseAssignment (values : α → Comp Common.model) : α → Inference.Comp contextualModel :=
  fun index => eraseComp (values index)

theorem row_eval (values : α → Comp Common.model) (row : RowTerm α) :
    (eraseRow row).eval contextualModel (eraseAssignment values) = row.eval Common.model values := by
  induction row <;> simp_all [eraseRow, Inference.RowTerm.eval, RowTerm.eval,
    eraseAssignment, eraseComp] <;> rfl

abbrev oldObservation (depth : Nat) (type : RegularInferenceModel.Ty Common.Row) :=
  type.eval (RegularValueTypes.observe (RegularInferenceModel.graph Common.Row) depth)

abbrev erasedObservation (depth : Nat) (type : Common.Ty) :=
  (CommonLegacyLayerErasure.erase [] type).eval
    (RegularValueTypes.observe (CommonLegacyRegularErasure.graph (CommonSyntax.graph Common.Row)) depth)

/-- Every default-free symbolic type commutes with erasure at every depth,
including exact empty and shared unknowns in negative positions. -/
theorem eval_translation_observe (term : TyTerm α) (good : clean term = true)
    (values : α → Comp Common.model) (depth : Nat) :
    oldObservation depth (eraseType (term.eval Common.model values)) =
      oldObservation depth ((translateType term).eval contextualModel (eraseAssignment values)) := by
  refine (eraseType_observe (Row := Common.Row) (term.eval Common.model values) depth).trans ?_
  change erasedObservation depth (term.eval Common.model values) = _
  induction term generalizing depth with
  | var index => exact (eraseType_observe (values index).1 depth).symm
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | recordDefault => cases good
  | union first last ihf ihl =>
      obtain ⟨firstGood, lastGood⟩ := Bool.and_eq_true_iff.mp good
      change StructuralBase.Ty.union (erasedObservation depth (first.eval Common.model values))
        (erasedObservation depth (last.eval Common.model values)) =
        .union (oldObservation depth ((translateType first).eval contextualModel (eraseAssignment values)))
          (oldObservation depth ((translateType last).eval contextualModel (eraseAssignment values)))
      rw [ihf firstGood, ihl lastGood]
  | inter first last ihf ihl =>
      obtain ⟨firstGood, lastGood⟩ := Bool.and_eq_true_iff.mp good
      change StructuralBase.Ty.inter (erasedObservation depth (first.eval Common.model values))
        (erasedObservation depth (last.eval Common.model values)) =
        .inter (oldObservation depth ((translateType first).eval contextualModel (eraseAssignment values)))
          (oldObservation depth ((translateType last).eval contextualModel (eraseAssignment values)))
      rw [ihf firstGood, ihl lastGood]
  | pair first last ihf ihl =>
      obtain ⟨firstGood, lastGood⟩ := Bool.and_eq_true_iff.mp good
      cases depth with
      | zero => rfl
      | succ depth =>
        change StructuralBase.Ty.pair (erasedObservation depth (first.eval Common.model values))
          (erasedObservation depth (last.eval Common.model values)) =
          .pair (oldObservation depth ((translateType first).eval contextualModel (eraseAssignment values)))
            (oldObservation depth ((translateType last).eval contextualModel (eraseAssignment values)))
        rw [ihf firstGood, ihl lastGood]
  | required label payload ih =>
      cases depth with
      | zero => rfl
      | succ depth =>
        change StructuralBase.Ty.record label (erasedObservation depth (payload.eval Common.model values))
          .emptyRecord = .record label
            (oldObservation depth ((translateType payload).eval contextualModel (eraseAssignment values))) .emptyRecord
        rw [ih good]
  | variant label payload ih =>
      cases depth with
      | zero => rfl
      | succ depth =>
        change StructuralBase.Ty.variant label (erasedObservation depth (payload.eval Common.model values)) =
          .variant label (oldObservation depth ((translateType payload).eval contextualModel (eraseAssignment values)))
        rw [ih good]
  | record label payload rest ihp ihr =>
      obtain ⟨payloadGood, restGood⟩ := Bool.and_eq_true_iff.mp good
      cases depth with
      | zero =>
        change StructuralBase.Ty.record label .bottom (erasedObservation 0 (rest.eval Common.model values)) =
          .record label .bottom (oldObservation 0 ((translateType rest).eval contextualModel (eraseAssignment values)))
        rw [ihr restGood]
      | succ depth =>
        change StructuralBase.Ty.record label (erasedObservation depth (payload.eval Common.model values))
          (erasedObservation (depth + 1) (rest.eval Common.model values)) =
          .record label (oldObservation depth ((translateType payload).eval contextualModel (eraseAssignment values)))
            (oldObservation (depth + 1) ((translateType rest).eval contextualModel (eraseAssignment values)))
        rw [ihp payloadGood, ihr restGood]
  | arrow input incoming output outgoing ihi iho =>
      obtain ⟨inputGood, outputGood⟩ := Bool.and_eq_true_iff.mp good
      cases depth with
      | zero =>
        change StructuralBase.Ty.arrow .bottom (incoming.eval Common.model values) .bottom
          (outgoing.eval Common.model values) = .arrow .bottom
            ((eraseRow incoming).eval contextualModel (eraseAssignment values)) .bottom
            ((eraseRow outgoing).eval contextualModel (eraseAssignment values))
        rw [row_eval, row_eval]
      | succ depth =>
        change StructuralBase.Ty.arrow (erasedObservation depth (input.eval Common.model values))
          (incoming.eval Common.model values) (erasedObservation depth (output.eval Common.model values))
          (outgoing.eval Common.model values) = .arrow
            (oldObservation depth ((translateType input).eval contextualModel (eraseAssignment values)))
            ((eraseRow incoming).eval contextualModel (eraseAssignment values))
            (oldObservation depth ((translateType output).eval contextualModel (eraseAssignment values)))
            ((eraseRow outgoing).eval contextualModel (eraseAssignment values))
        rw [ihi inputGood, iho outputGood, row_eval, row_eval]

/-- Translate an actually satisfied clean formula, constructing one erased
old computation for every existential slot and retaining every row. -/
theorem formula_reflected (formula : Formula α) (good : CleanFormula formula)
    (values : α → Comp Common.model) (held : formula.Holds Common.model values) :
    (translateFormula formula).Holds contextualModel (eraseAssignment values) := by
  induction formula with
  | top => trivial
  | bot => exact held
  | and first last ihf ihl => exact ⟨ihf good.1 values held.1, ihl good.2 values held.2⟩
  | or first last ihf ihl =>
      exact held.elim (fun proof => Or.inl (ihf good.1 values proof))
        (fun proof => Or.inr (ihl good.2 values proof))
  | tyLe source target =>
      have erased := eraseType_mono Common.rowLe (source.eval Common.model values)
        (target.eval Common.model values) held
      intro depth
      change ProducerContextual.ProducerLe Common.rowLe
        (oldObservation depth ((translateType source).eval contextualModel (eraseAssignment values)))
        (oldObservation depth ((translateType target).eval contextualModel (eraseAssignment values)))
      rw [← eval_translation_observe source good.1 values depth,
        ← eval_translation_observe target good.2 values depth]
      exact erased depth
  | rowLe source target =>
      change Common.rowLe ((eraseRow source).eval contextualModel (eraseAssignment values))
        ((eraseRow target).eval contextualModel (eraseAssignment values))
      rw [row_eval, row_eval]
      exact held
  | existsSlot body ih =>
      obtain ⟨witness, proof⟩ := held
      refine ⟨eraseComp witness, ?_⟩
      have extended : eraseAssignment (extend values witness) =
          Inference.extend (eraseAssignment values) (eraseComp witness) := by
        funext index
        cases index <;> rfl
      exact extended ▸ ih good (extend values witness) proof

/-- Reflection at every embedded old result for the entire required-field
source language. The old result computation, including its row, is fixed. -/
theorem typing_reflected (expression : Inference.Expr)
    (required : expression.requiredFieldsOnly = true) (target : Inference.Comp legacyModel)
    (typed : Typing Common.model [] expression (Common.embedComp target)) :
    Inference.Typing contextualModel [] expression target := by
  have original := (principal_exact Common.model expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) (Common.embedComp target)).mpr typed
  have cleanPrincipal := CommonLegacyGeneratedErasure.clean_principal expression required
    ([] : SchemeEnv Empty) (by intro _ member; cases member)
  have reflected := formula_reflected (principal ([] : SchemeEnv Empty) expression) cleanPrincipal
    (extend Empty.elim (Common.embedComp target)) original
  rw [CommonLegacyGenerationTranslation.principal_translation expression required] at reflected
  simp only [CommonLegacyGenerationTranslation.translateEnv, List.map_nil] at reflected
  have assignmentEqual : eraseAssignment (extend Empty.elim (Common.embedComp target)) =
      Inference.extend Empty.elim (eraseComp (Common.embedComp target)) := by
    funext index
    cases index with
    | none => rfl
    | some index => exact Empty.elim index
  rw [assignmentEqual] at reflected
  have oldTyped := (Inference.principal_exact contextualModel expression ([] : Inference.SchemeEnv Empty)
    [] Empty.elim (by intro index value; simp [Inference.SchemeLookup, Inference.BindingLookup])
    (eraseComp (Common.embedComp target))).mp reflected
  apply ConstraintProblems.typing_subsumption contextualModel
    ProducerContextualRegular.producerLe_trans Common.rowLe_refl Common.rowLe_trans oldTyped
  refine ⟨?_, Common.rowLe_refl _⟩
  intro depth
  change ProducerContextual.ProducerLe Common.rowLe
    (oldObservation depth (eraseType (Common.embedOld target.1))) (oldObservation depth target.1)
  have same := CommonLegacyRegularErasure.eraseType_embed_observe (Row := Common.Row) target.1 depth
  rw [show oldObservation depth (eraseType (Common.embedOld target.1)) = oldObservation depth target.1 from same]
  exact ProducerContextual.producerLe_refl _

end Yulang.CommonLegacySharedWitnesses
