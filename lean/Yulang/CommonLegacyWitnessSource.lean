import Yulang.CommonLegacyWitnessPositive
import Yulang.CommonLegacyEmbeddedWitnesses
import Yulang.CoreCommonInference

/-!
# Shared legacy witnesses for closed constructor sources

The source fragment below contains arbitrarily nested literals, empty records,
pairs, variants, first-field-wins records, branches and constant lambdas. There
is no variable constructor: every lambda body in the fragment is itself closed.

Intermediate types and rows in the original common derivation are completely
unrestricted. We reconstruct one type for the whole source, prove that it is
below the original result, and rebuild old contextual typing. Every old regular
target and every result row are retained. The actual generated-clause witness
and the actual old inference instance are then recovered by existing exactness
theorems. General lambda/application/let witness interpolation is not claimed.
-/

namespace Yulang.CommonLegacyWitnessSource

open Inference (Expr)
open CommonLegacyEmptyReflection (legacyModel contextualModel)
open CommonLegacyWitnessPositive (OldTy OldLe Agrees)

/-- A syntactic sublanguage of the existing source AST. Lambda bodies contain
no variables, so the argument is not used, including through nested closures. -/
inductive ClosedConstructors : Expr → Prop where
  | lit (scalar : Inference.Base) : ClosedConstructors (.lit scalar)
  | emptyRecord : ClosedConstructors .emptyRecord
  | pair : ClosedConstructors first → ClosedConstructors last → ClosedConstructors (.pair first last)
  | variant (label : Nat) : ClosedConstructors payload → ClosedConstructors (.variant label payload)
  | record (label : Nat) : ClosedConstructors payload → ClosedConstructors rest →
      ClosedConstructors (.record label payload rest)
  | branch : ClosedConstructors condition → ClosedConstructors yes → ClosedConstructors no →
      ClosedConstructors (.branch condition yes no)
  | lam : ClosedConstructors body → ClosedConstructors (.lam body)

/-- An unused argument accepts every occurrence. This is an explicit old and
common row, used only in the proof's reconstructed constant-function type. -/
def allOccurrences : Common.Row := fun _ => True

/-- Constructor witnesses, not an alternative inference entry. Values outside
`ClosedConstructors` are unused by every theorem in this module. -/
def commonValue : Expr → Common.Ty
  | .lit scalar => .base scalar
  | .emptyRecord => Common.exactEmpty
  | .pair first last => Common.pair (commonValue first) (commonValue last)
  | .variant label payload => Common.variant label (commonValue payload)
  | .record label payload rest => Common.record label (commonValue payload) (commonValue rest)
  | .branch _ yes no => .union (commonValue yes) (commonValue no)
  | .lam body => Common.arrow .top allOccurrences (commonValue body) Common.rowEmpty
  | _ => .bottom

def legacyValue : Expr → OldTy
  | .lit scalar => .base scalar
  | .emptyRecord => .emptyRecord
  | .pair first last => .pair (.node (legacyValue first)) (.node (legacyValue last))
  | .variant label payload => .variant label (.node (legacyValue payload))
  | .record label payload rest => .record label (.node (legacyValue payload)) (legacyValue rest)
  | .branch _ yes no => .union (legacyValue yes) (legacyValue no)
  | .lam body => .arrow (.node .top) allOccurrences (.node (legacyValue body)) Common.rowEmpty
  | _ => .bottom

theorem requiredFieldsOnly {expression : Expr} (closed : ClosedConstructors expression) :
    expression.requiredFieldsOnly = true := by
  induction closed <;> simp_all [Expr.requiredFieldsOnly]

/-- Agreement is derived from syntax, never imposed on the original common
witnesses or on a public scheme's parameters. -/
theorem value_agrees {expression : Expr} (closed : ClosedConstructors expression) :
    Agrees (commonValue expression) (legacyValue expression) := by
  induction closed with
  | lit scalar => exact Agrees.base scalar
  | emptyRecord => exact Agrees.exactEmpty
  | pair _ _ left right => exact Agrees.pair left right
  | variant label _ payload => exact Agrees.variant label payload
  | record label _ _ payload remaining => exact Agrees.record label payload remaining
  | branch _ _ _ _ yes no => exact Agrees.union yes no
  | lam _ body => exact Agrees.arrow .top allOccurrences Common.rowEmpty body

private theorem old_subsume {environment : List (Inference.Binding contextualModel)}
    {expression : Expr} {source target : Inference.Comp contextualModel}
    (typed : Inference.Typing contextualModel environment expression source)
    (bounded : Inference.Comp.le contextualModel source target) :
    Inference.Typing contextualModel environment expression target :=
  ConstraintProblems.typing_subsumption contextualModel
    ProducerContextualRegular.producerLe_trans Common.rowLe_refl Common.rowLe_trans typed bounded

private theorem joined_empty : Common.rowLe (Common.rowJoin Common.rowEmpty Common.rowEmpty) Common.rowEmpty :=
  (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩

/-- For every source in the fragment, every common environment and result, and
every old environment, an arbitrary common derivation yields a reconstructed
old derivation and a common lower bound for its original result. Environments
need not be related because these sources have no free or bound variable uses. -/
theorem reconstruct {expression : Expr} (closed : ClosedConstructors expression)
    (environment : List (Core.PresenceGeneration.Binding Common.model))
    (oldEnvironment : List (Inference.Binding contextualModel))
    (result : Core.PresenceGeneration.Comp Common.model)
    (typed : Core.PresenceGeneration.Typing Common.model environment expression result) :
    Common.Subtype (commonValue expression) result.1 ∧
      Inference.Typing contextualModel oldEnvironment expression
        (legacyValue expression, Common.rowEmpty) := by
  induction closed generalizing environment oldEnvironment result with
  | lit scalar =>
      cases typed with
      | lit bounded =>
          exact ⟨bounded.1, .lit ⟨ProducerContextualRegular.producerLe_refl _, Common.rowLe_refl _⟩⟩
  | emptyRecord =>
      cases typed with
      | emptyRecord bounded =>
          exact ⟨bounded.1, .emptyRecord ⟨ProducerContextualRegular.producerLe_refl _, Common.rowLe_refl _⟩⟩
  | pair first last left right =>
      cases typed with
      | pair firstTyped lastTyped bounded =>
          obtain ⟨firstBelow, firstOld⟩ := left environment oldEnvironment _ firstTyped
          obtain ⟨lastBelow, lastOld⟩ := right environment oldEnvironment _ lastTyped
          exact ⟨Common.subtype_trans ((Common.common_pair_iff _ _ _ _).mpr ⟨firstBelow, lastBelow⟩) bounded.1,
            .pair firstOld lastOld ⟨ProducerContextualRegular.producerLe_refl _, joined_empty⟩⟩
  | variant label payload ih =>
      cases typed with
      | variant payloadTyped bounded =>
          obtain ⟨payloadBelow, payloadOld⟩ := ih environment oldEnvironment _ payloadTyped
          exact ⟨Common.subtype_trans ((Common.common_variant_iff label _ _).mpr payloadBelow) bounded.1,
            .variant payloadOld ⟨ProducerContextualRegular.producerLe_refl _, Common.rowLe_refl _⟩⟩
  | record label payload rest headIH restIH =>
      cases typed with
      | record payloadTyped restTyped shape bounded =>
          obtain ⟨payloadBelow, payloadOld⟩ := headIH environment oldEnvironment _ payloadTyped
          obtain ⟨restBelow, restOld⟩ := restIH environment oldEnvironment _ restTyped
          have oldShape := (value_agrees rest).upper_reflected .emptyRecord
            (Common.subtype_trans restBelow shape)
          exact ⟨Common.subtype_trans (Common.common_record_mono label payloadBelow restBelow) bounded.1,
            .record payloadOld restOld oldShape ⟨ProducerContextualRegular.producerLe_refl _, joined_empty⟩⟩
  | branch condition yes no conditionIH yesIH noIH =>
      cases typed with
      | branch conditionTyped yesTyped noTyped bounded =>
          obtain ⟨conditionBelow, conditionOld⟩ := conditionIH environment oldEnvironment _ conditionTyped
          obtain ⟨yesBelow, yesOld⟩ := yesIH environment oldEnvironment _ yesTyped
          obtain ⟨noBelow, noOld⟩ := noIH environment oldEnvironment _ noTyped
          have oldCondition : Inference.Typing contextualModel oldEnvironment _
              (.base .bool, Common.rowEmpty) := old_subsume conditionOld
            ⟨(value_agrees condition).upper_reflected (.base .bool) conditionBelow, Common.rowLe_refl _⟩
          exact ⟨Common.subtype_trans (Common.common_union_mono yesBelow noBelow) bounded.1,
            .branch oldCondition yesOld noOld
              ⟨ProducerContextualRegular.producerLe_refl _,
                (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_refl _, joined_empty⟩⟩⟩
  | lam body ih =>
      cases typed with
      | lam bodyTyped bounded =>
          obtain ⟨bodyBelow, bodyOld⟩ := ih _
            (.mono (.top, allOccurrences) :: oldEnvironment) _ bodyTyped
          refine ⟨?_, .lam bodyOld ⟨ProducerContextualRegular.producerLe_refl _, Common.rowLe_refl _⟩⟩
          apply Common.subtype_trans ?_ bounded.1
          exact (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
            ⟨CommonBoundCoalescing.le_top _, (fun _ _ => True.intro), bodyBelow, Common.rowEmpty_le _⟩

/-- All old regular targets and all result rows, with no inference-support,
solver-success or restriction on the common typing witnesses. -/
theorem typing_exact (expression : Expr) (closed : ClosedConstructors expression)
    (target : Inference.Comp legacyModel) :
    Core.PresenceGeneration.Typing Common.model [] expression (Common.embedComp target) ↔
      Inference.Typing contextualModel [] expression target := by
  constructor
  · intro typed
    obtain ⟨bounded, reconstructed⟩ := reconstruct closed [] [] _ typed
    exact old_subsume reconstructed
      ⟨(value_agrees closed).upper_reflected target.1 bounded, Common.rowEmpty_le target.2⟩
  · exact CommonLegacyEmbeddedWitnesses.contextual_typing_preserved expression (requiredFieldsOnly closed) target

/-- The actual presence generator admits one shared old assignment for every
common typing at an old result. Only the source sublanguage is restricted. -/
theorem shared_witness_recovery (expression : Expr) (closed : ClosedConstructors expression)
    (target : Inference.Comp legacyModel)
    (typed : Core.PresenceGeneration.Typing Common.model [] expression (Common.embedComp target)) :
    ∃ clause ∈ PresenceNormalForm.normalise
        (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression),
      ∃ values : Fin (clause.locals + 1) → Inference.Comp legacyModel,
        values (Fin.last clause.locals) = target ∧
          PresenceNormalForm.All Common.model (CommonLegacyTyping.assignment values) clause.pack :=
  (CommonLegacyEmbeddedWitnesses.embedded_witnesses_iff_typing expression
    (requiredFieldsOnly closed) target).mpr ((typing_exact expression closed target).mp typed)

/-- Decision 46 for the stated closed constructor sublanguage, at the actual
new and old inference entries. The requested old result row is preserved
literally; the value is recovered up to the independent demand equivalence. -/
theorem legacy_instances_reflected (expression : Expr) (closed : ClosedConstructors expression)
    (supported : SourcePrincipalInference.supported expression = true)
    (target : Inference.Comp legacyModel)
    (accepted : (Core.infer (Core.Required.embed expression)).Instance (Common.embedComp target)) :
    ∃ old : Inference.Comp legacyModel,
      (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra old ∧
        Common.Equivalent (Common.embedOld target.1) (Common.embedOld old.1) ∧ target.2 = old.2 := by
  have sourceTyped := (CommonSolvedSource.source_principal expression (Common.embedComp target)).mpr
    (by simpa only [Core.infer_embed, Core.CommonInference.Result.Instance,
      Core.CommonInference.Result.mem_schemes, Core.CommonInference.finish_schemes] using accepted)
  exact CommonLegacyEmptyReflection.contextual_typing_legacy_reflected expression supported target
    ((typing_exact expression closed target).mp sourceTyped)

end Yulang.CommonLegacyWitnessSource
