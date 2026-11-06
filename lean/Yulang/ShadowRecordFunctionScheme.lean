import Yulang.RigidRecordFunctionScheme
import Yulang.ShadowRecordValueInference

/-!
# The existing open-record function scheme after hidden-field equality

The source expression, computed descriptor and freely instantiated parameters
are reused from `RigidRecordFunctionScheme`. Completeness is reproved against
all typings of the decision-40 relation, rather than merely transporting old
instances. This remains the family `fun r => record label literal r`, not an
inference algorithm for arbitrary functions.
-/

namespace Yulang.ShadowRecordFunctionScheme

open Inference
open StructuralBase (Ty)
open ShadowSemanticRecords (Subtype Equivalent)
open ShadowRecordValueInference (model clamp_retract widen_retract)
open RigidRecordFunctionScheme (source scheme Parameters inputType headType tailType instantiate Instance)

universe u
variable {Row : Type u}

theorem input_retract {leRow : Row → Row → Prop} {input : Ty Row}
    (admissible : Subtype leRow input .emptyRecord) :
    Equivalent leRow (.inter input .emptyRecord) input :=
  ⟨.interLeft _ _, .interIntro (.refl _) admissible⟩

/-- All three value parameters and the row are entirely free. -/
theorem instantiate_sound (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (parameter : Parameters (model algebra)) :
    Typing (model algebra) [] (source label base) (instantiate (model algebra) label base parameter) := by
  apply Typing.lam
    (a := (inputType (model algebra) parameter, parameter.row))
    (b := ((model algebra).record label (headType (model algebra) base parameter)
      (tailType (model algebra) parameter), parameter.row))
  · apply Typing.record
      (a := (headType (model algebra) base parameter, algebra.empty))
      (b := (tailType (model algebra) parameter, parameter.row))
    · exact .lit ⟨.unionLeft _ _, algebra.refl _⟩
    · exact .var rfl (.mono ⟨Subtype.interIntro (.unionLeft _ _) (.interRight _ _), algebra.refl _⟩)
    · exact .interRight _ _
    · exact ⟨.refl _, (algebra.join_le_iff _ _ _).mpr ⟨algebra.empty_le _, algebra.refl _⟩⟩
  · exact ⟨.refl _, algebra.refl _⟩

/-- The source typing itself supplies the parameter tuple. Its widened head
and tail are retained; the input computation row is shared in both arrow
positions, with later output-row widening handled by ordinary subtyping. -/
theorem typing_complete (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) (typed : Typing (model algebra) [] (source label base) target) :
    Instance (model algebra) label base target := by
  cases typed with
  | lam bodyTyped outerBound =>
      rename_i input result
      cases bodyTyped with
      | record headTyped tailTyped admissible bodyBound =>
          rename_i head tail
          cases headTyped with
          | lit headBound =>
              cases tailTyped with
              | var found bindingTyped =>
                  cases found
                  cases bindingTyped with
                  | mono tailBound =>
                      let parameter : Parameters (model algebra) := ⟨input.1, head.1, tail.1, input.2⟩
                      have inputEqual := input_retract (.trans tailBound.1 admissible)
                      have headEqual := widen_retract headBound.1
                      have tailEqual := clamp_retract (.trans inputEqual.1 tailBound.1) admissible
                      have outputBelow := Subtype.trans
                        (ShadowSemanticRecords.record_congr label headEqual tailEqual).1 bodyBound.1
                      have rowBelow := algebra.trans tailBound.2
                        ((algebra.join_le_iff _ _ _).mp bodyBound.2).2
                      exact ⟨parameter,
                        .trans (.arrow inputEqual.2 (algebra.refl _) outputBelow rowBelow) outerBound.1,
                        outerBound.2⟩

/-- Full principal instance equality for the original open-tail function
family. No success, typing, or parameter constraint is a premise. -/
theorem instances_exact (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    Instance (model algebra) label base target ↔ Typing (model algebra) [] (source label base) target := by
  constructor
  · rintro ⟨parameter, bounded⟩
    exact ConstraintProblems.typing_subsumption (model algebra) Subtype.trans algebra.refl
      (fun first last => algebra.trans first last) (instantiate_sound algebra label base parameter) bounded
  · exact typing_complete algebra label base target

theorem principal_formula_exact (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    Instance (model algebra) label base target ↔
      (principal ([] : SchemeEnv Empty) (source label base)).Holds
        (model algebra) (extend Empty.elim target) :=
  (instances_exact algebra label base target).trans
    (principal_exact (model algebra) (source label base) [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

/-- In particular the scheme retains the same arbitrary admissible record
and the same arbitrary row on input and output, even when the record is not
equivalent to a rigid spine. -/
theorem diagonal_instance (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (record : Ty Row) (row : Row) (admissible : Subtype algebra.le record .emptyRecord) :
    Instance (model algebra) label base
      (.arrow record row (.record label (.base base) record) row, algebra.empty) := by
  let parameter : Parameters (model algebra) := ⟨record, .base base, record, row⟩
  have inputEqual := input_retract admissible
  have resultEqual := ShadowSemanticRecords.record_congr label (widen_retract (.refl (.base base)))
    (clamp_retract inputEqual.1 admissible)
  exact ⟨parameter, .arrow inputEqual.2 (algebra.refl _) resultEqual.1 (algebra.refl _), algebra.refl _⟩

end Yulang.ShadowRecordFunctionScheme
