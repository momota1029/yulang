import Yulang.ShadowRecordFunctionScheme
import Yulang.RigidRecordFunctionQuotient
import Yulang.ShadowRecordValueQuotient

/-!
# The open-tail function scheme on semantic type classes

The finite descriptor computed by `RigidRecordFunctionScheme.scheme` is
unchanged. Its three value parameters range over all quotient types, and its
row parameter ranges over the whole row algebra. Exact transport retains all
instances in the latest shadow-erasure relation, without adding tail covariance.
-/

namespace Yulang.ShadowRecordFunctionQuotient

open Inference
open RigidRecordFunctionScheme (Parameters source scheme instantiate Instance)

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  ShadowRecordQuotientInference.model algebra

theorem raw_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (label : Nat) (base : Base) (result : Comp (ShadowRecordValueInference.model algebra)) :
    Instance (model algebra) label base (ShadowRecordQuotient.mk result.1, result.2) ↔
      Instance (ShadowRecordValueInference.model algebra) label base result :=
  RigidRecordFunctionQuotient.instances_transport
    (ShadowRecordQuotientInference.quotientMap algebra.empty algebra.join algebra.le algebra.refl)
    (fun proof => proof) (fun proof => proof)
    (ShadowRecordValueQuotient.value_surjective algebra.le) (fun row => ⟨row, rfl⟩)
    label base result

/-- The premise is just a row join algebra. The label, literal base and
target computation are arbitrary, including targets with opaque tails. -/
theorem instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (label : Nat) (base : Base) (target : Comp (model algebra)) :
    Instance (model algebra) label base target ↔
      Typing (model algebra) [] (source label base) target := by
  rcases target with ⟨value, row⟩
  refine Quotient.inductionOn value ?_
  intro representative
  exact (raw_instances_exact algebra label base (representative, row)).trans
    ((ShadowRecordFunctionScheme.instances_exact algebra label base (representative, row)).trans
      (ShadowRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
        algebra.le algebra.refl (source label base) (representative, row)).symm)

theorem principal_formula_exact (algebra : RowFlowSchemes.Algebra Row)
    (label : Nat) (base : Base) (target : Comp (model algebra)) :
    Instance (model algebra) label base target ↔
      (principal ([] : SchemeEnv Empty) (source label base)).Holds
        (model algebra) (extend Empty.elim target) :=
  (instances_exact algebra label base target).trans
    (principal_exact (model algebra) (source label base) [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

/-- Every tuple of three semantic value types and one row gives a valid
instance of the unchanged source function. No parameter constraint remains. -/
theorem instantiate_sound (algebra : RowFlowSchemes.Algebra Row)
    (label : Nat) (base : Base) (parameter : Parameters (model algebra)) :
    Typing (model algebra) [] (source label base)
      (instantiate (model algebra) label base parameter) :=
  (instances_exact algebra label base _).mp
    ⟨parameter, ShadowRecordQuotient.le_refl _, algebra.refl _⟩

end Yulang.ShadowRecordFunctionQuotient
