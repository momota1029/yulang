import Yulang.ContextualSourcePrincipalInference
import Yulang.CoreSourceInference
import Yulang.CoreProducerContextualInstances

/-!
# Core completeness and legacy reflection in the contextual model

The executable entry is exactly `Core.RequiredInference.infer`, interpreted
through contextual producer instances. Its source support boundary is retained.
The independent Core judgment is `Core.Required` over the concrete contextual
regular model; no solver instance occurs in that judgment's definition.

The direct free-parameter family is definitionally the one previously exposed
by `Core.ProducerContextualInstances`. Consequently its missing converse from
independent new typing is now proved for every old supported source. Combining
this exactness with the established legacy-family theorem gives preservation
and reflection up to demand equality, with the requested result row unchanged.

This is the required-field source/Core fragment. Presence exact/default rules
and a combined presence entry are separate contracts, not changed here.
-/

namespace Yulang.Core.ContextualRequiredInference

open Inference (Comp)

variable {Row : Type}

abbrev Term := Required.Term
abbrev Result := SourcePrincipalInference.Result
abbrev model := @ContextualSourcePrincipalInference.model
abbrev infer := RequiredInference.infer
abbrev Instance (algebra : RowFlowSchemes.Algebra Row) (result : Result) (target : Comp (model algebra)) :=
  ContextualSourcePrincipalInference.Result.Instance algebra target result

def supported (expression : Term) : Bool :=
  InferenceSyntax.supported expression &&
    ContextualSourcePrincipalInference.supported (Required.decode expression)

abbrev RecordFree := RequiredInference.RecordFree

theorem infer_embed (expression : Inference.Expr) :
    infer (Required.embed expression) = ContextualSourcePrincipalInference.infer expression :=
  RequiredInference.infer_embed expression

theorem infer_unsupported_iff (expression : Term) :
    (infer expression).status = .unsupported ↔ supported expression = false := by
  cases syntaxChecked : InferenceSyntax.supported expression with
  | false => simp [infer, RequiredInference.infer, supported, syntaxChecked, SourcePrincipalInference.Result.status]
  | true =>
      simpa only [infer, RequiredInference.infer, supported, syntaxChecked, ↓reduceIte, Bool.true_and] using
        ContextualSourcePrincipalInference.infer_unsupported_iff (Required.decode expression)

/-- Every old supported Core expression and every regular value/row target
have exactly the directly evaluated contextual instances of the actual entry. -/
theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Term) (checked : supported expression = true) (target : Comp (model algebra)) :
    Instance algebra (infer expression) target ↔
      Typing (Required.model (model algebra)) [] expression target := by
  obtain ⟨syntaxChecked, sourceChecked⟩ := Bool.and_eq_true_iff.mp checked
  rw [infer, RequiredInference.infer, ite_eq_left syntaxChecked]
  exact (ContextualSourcePrincipalInference.infer_instances_exact algebra rowAntisymm
    (Required.decode expression) sourceChecked target).trans (by
      simpa only [List.map_nil, InferenceSyntax.embed_decode expression syntaxChecked] using
        Required.conservative (model algebra) [] (Required.decode expression) target)

/-- This is the explicit principal form: only returned alternatives and free
row/value parameters precede the final contextual subsumption comparison. -/
theorem principal_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Term) (checked : supported expression = true) (target : Comp (model algebra)) :
    Typing (Required.model (model algebra)) [] expression target ↔
      ∃ principal, infer expression = .inferred principal ∧
        ∃ alternative ∈ principal,
          ∃ rows : Fin alternative.slots → Row,
          ∃ values : Fin alternative.scheme.size → RegularInferenceModel.Ty Row,
            Comp.le (model algebra)
              (alternative.scheme.instantiate algebra rows values alternative.output) target := by
  rw [← infer_instances_exact algebra rowAntisymm expression checked target]
  cases infer expression <;> simp [Instance, ContextualSourcePrincipalInference.Result.Instance,
    ContextualSourcePrincipalInference.Principal.Instance, ContextualSourcePrincipalInference.Alternative.Instance,
    ContextualJointConstraintInference.Scheme.Instance]

theorem infer_rejected_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Term) :
    (infer expression).status = .rejected ↔ supported expression = true ∧
      ¬ ∃ target, Typing (Required.model (model algebra)) [] expression target := by
  cases syntaxChecked : InferenceSyntax.supported expression with
  | false => simp [infer, RequiredInference.infer, supported, syntaxChecked, SourcePrincipalInference.Result.status]
  | true =>
      have exactTyping (target : Comp (model algebra)) :
          Inference.Typing (model algebra) [] (Required.decode expression) target ↔
            Typing (Required.model (model algebra)) [] expression target := by
        simpa only [List.map_nil, InferenceSyntax.embed_decode expression syntaxChecked] using
          Required.conservative (model algebra) [] (Required.decode expression) target
      rw [infer, RequiredInference.infer, ite_eq_left syntaxChecked,
        ContextualSourcePrincipalInference.infer_rejected_iff algebra rowAntisymm (Required.decode expression)]
      simp only [supported, syntaxChecked, Bool.true_and]
      apply and_congr_right
      intro _
      exact not_congr (exists_congr exactTyping)

theorem recordFree_supported (expression : Term) (fragment : RecordFree expression) :
    supported expression = true :=
  Bool.and_eq_true_iff.mpr ⟨fragment.1,
    ContextualSourcePrincipalInference.recordFree_supported (Required.decode expression) fragment.2⟩

theorem recordFree_ne_unsupported (expression : Term) (fragment : RecordFree expression) :
    (infer expression).status ≠ .unsupported := by
  intro absent
  have failed := (infer_unsupported_iff expression).mp absent
  rw [recordFree_supported expression fragment] at failed
  cases failed

/-- The only source restriction is syntactic `RecordFree`; no successful
inference, solver solution, cache or support-check result is supplied. -/
theorem recordFree_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Term) (fragment : RecordFree expression) (target : Comp (model algebra)) :
    Instance algebra (infer expression) target ↔ Typing (Required.model (model algebra)) [] expression target :=
  infer_instances_exact algebra rowAntisymm expression (recordFree_supported expression fragment) target

theorem recordFree_principal (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Term) (fragment : RecordFree expression) (target : Comp (model algebra)) :
    Typing (Required.model (model algebra)) [] expression target ↔
      ∃ principal, infer expression = .inferred principal ∧
        ∃ alternative ∈ principal,
          ∃ rows : Fin alternative.slots → Row,
          ∃ values : Fin alternative.scheme.size → RegularInferenceModel.Ty Row,
            Comp.le (model algebra)
              (alternative.scheme.instantiate algebra rows values alternative.output) target :=
  principal_exact algebra rowAntisymm expression (recordFree_supported expression fragment) target

theorem recordFree_rejected_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Term) (fragment : RecordFree expression) :
    (infer expression).status = .rejected ↔
      ¬ ∃ target, Typing (Required.model (model algebra)) [] expression target := by
  simpa only [recordFree_supported expression fragment, true_and] using
    infer_rejected_iff algebra rowAntisymm expression

/-- The previous direct migration family and the new source interpretation
evaluate exactly the same finite schemes and all of the same parameters. -/
theorem producerInstance_iff (algebra : RowFlowSchemes.Algebra Row)
    (result : Result) (target : Comp (model algebra)) :
    Instance algebra result target ↔ ProducerContextualInstances.Instance algebra result target := by
  cases result <;> rfl

/-- This is the previously missing converse, now an iff for all old supported
sources and all old-carrier result values/rows in the contextual model. -/
theorem legacy_source_typing_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Inference.Expr) (checked : SourcePrincipalInference.supported expression = true)
    (target : Comp (model algebra)) :
    ProducerContextualInstances.Instance algebra (SourcePrincipalInference.infer expression) target ↔
      Inference.Typing (model algebra) [] expression target :=
  (producerInstance_iff algebra _ target).symm.trans
    (ContextualSourcePrincipalInference.infer_instances_exact algebra rowAntisymm expression checked target)

theorem legacy_core_typing_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Inference.Expr) (checked : SourcePrincipalInference.supported expression = true)
    (target : Comp (model algebra)) :
    ProducerContextualInstances.Instance algebra (SourcePrincipalInference.infer expression) target ↔
      Typing (Required.model (model algebra)) [] (Required.embed expression) target :=
  (legacy_source_typing_exact algebra rowAntisymm expression checked target).trans (by
    simpa only [List.map_nil] using Required.conservative (model algebra) [] expression target)

/-- Independent new source typing is exactly old typing up to demand equality
of the result value. The result row is kept literally unchanged. -/
theorem source_typing_exact_modulo (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Inference.Expr) (checked : SourcePrincipalInference.supported expression = true)
    (target : Comp (model algebra)) :
    Inference.Typing (model algebra) [] expression target ↔
      ∃ oldValue : RegularInferenceModel.Ty Row,
        Inference.Typing (SourcePrincipalInference.model algebra) [] expression (oldValue, target.2) ∧
          ProducerContextualInstances.Equivalent algebra oldValue target.1 :=
  (legacy_source_typing_exact algebra rowAntisymm expression checked target).symm.trans
    (ProducerContextualInstances.source_instances_exact_modulo algebra rowAntisymm expression checked target)

theorem core_typing_exact_modulo (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Inference.Expr) (checked : SourcePrincipalInference.supported expression = true)
    (target : Comp (model algebra)) :
    Typing (Required.model (model algebra)) [] (Required.embed expression) target ↔
      ∃ oldValue : RegularInferenceModel.Ty Row,
        Typing (Required.model (SourcePrincipalInference.model algebra)) []
          (Required.embed expression) (oldValue, target.2) ∧
          ProducerContextualInstances.Equivalent algebra oldValue target.1 := by
  rw [← legacy_core_typing_exact algebra rowAntisymm expression checked target]
  rw [ProducerContextualInstances.source_instances_exact_modulo algebra rowAntisymm expression checked target]
  apply exists_congr
  intro oldValue
  apply and_congr_left
  intro _
  simpa only [List.map_nil] using
    Required.conservative (SourcePrincipalInference.model algebra) [] expression (oldValue, target.2)

end Yulang.Core.ContextualRequiredInference
