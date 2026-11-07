import Yulang.CoreInferenceSyntax
import Yulang.SourcePrincipalInference

/-! Executable Core access to the existing regular required-field solver.
This retains its type model and support boundary. It is not the presence-aware
M1 solver: `recordDefault` still returns `unsupported`. -/
namespace Yulang.Core.RequiredInference

open Inference (Comp)
-- M0's `Core.TypingModel` has context and result in `Type`.
variable {Row : Type}
abbrev Term := Required.Term
abbrev Result := SourcePrincipalInference.Result
abbrev model := @SourcePrincipalInference.model

def infer (e : Term) : Result :=
  if InferenceSyntax.supported e then SourcePrincipalInference.infer (Required.decode e)
  else .unsupported

/-- Exact result equality for every legacy input, including rejections and
unsupported inputs. Every retained scheme and all parameters are unchanged. -/
@[simp] theorem infer_embed (e : Inference.Expr) :
    infer (Required.embed e) = SourcePrincipalInference.infer e := by
  simp [infer]

theorem legacy_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (e : Inference.Expr) (c : Comp (model algebra)) :
    (infer (Required.embed e)).Instance algebra c ↔
      (SourcePrincipalInference.infer e).Instance algebra c := by rw [infer_embed]

/-- Every source solved by the old entry, including supported record sources,
retains exactly its Core typings in the unchanged required-field model. -/
theorem legacy_inferred_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (e : Inference.Expr) (principal : SourcePrincipalInference.Principal)
    (returned : SourcePrincipalInference.infer e = .inferred principal)
    (c : Comp (model algebra)) :
    principal.Instance algebra c ↔ Typing (Required.model (model algebra)) [] (Required.embed e) c :=
  (SourcePrincipalInference.infer_inferred_exact algebra rowAntisymm e principal returned c).trans (by
    simpa only [List.map_nil] using Required.conservative (model algebra) [] e c)

/-- A syntax-only fragment. Record construction and defaults are excluded;
lambda/app/let/branch/pair/projections/field/variant/lit/emptyRecord remain. -/
def RecordFree (e : Term) : Prop :=
  InferenceSyntax.supported e = true ∧ SourceConstraintSupport.RecordFree (Required.decode e)

theorem recordFree_ne_unsupported (e : Term) (fragment : RecordFree e) :
    (infer e).status ≠ .unsupported := by
  simpa [infer, fragment.1] using
    SourcePrincipalInference.recordFree_ne_unsupported (Required.decode e) fragment.2

/-- All closed source terms in the syntax fragment and every regular value /
row target. Only row antisymmetry and syntax membership are hypotheses. -/
theorem recordFree_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (e : Term) (fragment : RecordFree e) (c : Comp (model algebra)) :
    (infer e).Instance algebra c ↔ Typing (Required.model (model algebra)) [] e c := by
  rw [infer, ite_eq_left fragment.1]
  exact (SourcePrincipalInference.recordFree_instances_exact algebra rowAntisymm
    (Required.decode e) fragment.2 c).trans (by
      simpa only [List.map_nil, InferenceSyntax.embed_decode e fragment.1] using
        Required.conservative (model algebra) [] (Required.decode e) c)

/-- The explicit scheme/parameter/subsumption form, with unrestricted row
and regular value parameters and no residual model or solver assumptions. -/
theorem recordFree_principal (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (e : Term) (fragment : RecordFree e) (c : Comp (model algebra)) :
    Typing (Required.model (model algebra)) [] e c ↔
      ∃ principal, infer e = .inferred principal ∧
        ∃ alternative ∈ principal,
          ∃ rows : Fin alternative.slots → Row,
          ∃ values : Fin alternative.scheme.size → JointConstraintInference.Value Row,
            Comp.le (model algebra)
              (alternative.scheme.instantiate algebra rows values alternative.output) c := by
  rw [← recordFree_instances_exact algebra rowAntisymm e fragment c]
  cases infer e <;> simp [SourcePrincipalInference.Result.Instance,
    SourcePrincipalInference.Principal.Instance, SourcePrincipalInference.Alternative.Instance,
    JointConstraintInference.Scheme.Instance]

theorem recordFree_rejected_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (e : Term) (fragment : RecordFree e) :
    (infer e).status = .rejected ↔
      ¬ ∃ c, Typing (Required.model (model algebra)) [] e c := by
  have exactTyping (c : Comp (model algebra)) :
      Inference.Typing (model algebra) [] (Required.decode e) c ↔
        Typing (Required.model (model algebra)) [] e c := by
    simpa only [List.map_nil, InferenceSyntax.embed_decode e fragment.1] using
      Required.conservative (model algebra) [] (Required.decode e) c
  rw [infer, ite_eq_left fragment.1,
    SourcePrincipalInference.recordFree_rejected_iff algebra rowAntisymm (Required.decode e) fragment.2]
  constructor
  · rintro absent ⟨c, typed⟩
    exact absent ⟨c, (exactTyping c).mpr typed⟩
  · rintro absent ⟨c, typed⟩
    exact absent ⟨c, (exactTyping c).mp typed⟩

end Yulang.Core.RequiredInference
