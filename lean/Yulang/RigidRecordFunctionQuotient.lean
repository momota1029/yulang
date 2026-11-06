import Yulang.RigidRecordFunctionScheme
import Yulang.RigidRecordValueQuotient

/-!
# The open-tail function scheme on semantic type classes

The finite descriptor computed by `RigidRecordFunctionScheme.scheme` is
unchanged. Its three value parameters range over all quotient types, and its
row parameter ranges over the whole row algebra. Exact transport retains all
instances of the original closed function, without adding tail covariance.
-/

namespace Yulang.RigidRecordFunctionQuotient

open Inference
open RigidRecordFunctionScheme (Parameters source scheme instantiate Instance)

universe u

variable {Row : Type u}

abbrev model (algebra : RowFlowSchemes.Algebra Row) : Model :=
  RigidRecordQuotientInference.model algebra

theorem instances_transport (map : ModelMap sourceModel targetModel)
    (valueReflect : ∀ {a b}, targetModel.subTy (map.value a) (map.value b) → sourceModel.subTy a b)
    (rowReflect : ∀ {a b}, targetModel.subRow (map.row a) (map.row b) → sourceModel.subRow a b)
    (valueOnto : ∀ target, ∃ original, map.value original = target)
    (rowOnto : ∀ target, ∃ original, map.row original = target)
    (label : Nat) (base : Base) (result : Comp sourceModel) :
    Instance targetModel label base (map.comp result) ↔ Instance sourceModel label base result := by
  constructor
  · rintro ⟨parameter, below⟩
    obtain ⟨original, rfl⟩ := parameter.map_surjective map valueOnto rowOnto
    rw [← RigidRecordFunctionScheme.instantiate_map] at below
    exact ⟨original, valueReflect below.1, rowReflect below.2⟩
  · rintro ⟨parameter, below⟩
    refine ⟨parameter.map map, ?_⟩
    rw [← RigidRecordFunctionScheme.instantiate_map]
    exact ⟨map.subtype below.1, map.subrow below.2⟩

theorem raw_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (label : Nat) (base : Base) (result : Comp (RigidRecordValueInference.model algebra)) :
    Instance (model algebra) label base (RigidRecordQuotient.mk result.1, result.2) ↔
      Instance (RigidRecordValueInference.model algebra) label base result :=
  instances_transport
    (RigidRecordQuotientInference.quotientMap algebra.empty algebra.join algebra.le algebra.refl)
    (fun proof => proof) (fun proof => proof)
    (RigidRecordValueQuotient.value_surjective algebra.le) (fun row => ⟨row, rfl⟩)
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
    ((RigidRecordFunctionScheme.instances_exact algebra label base (representative, row)).trans
      (RigidRecordQuotientInference.closed_typing_exact algebra.empty algebra.join
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
    ⟨parameter, RigidRecordQuotient.le_refl _, algebra.refl _⟩

end Yulang.RigidRecordFunctionQuotient
