import Yulang.CommonCaseRecordDefaultFamily

/-! A default-only source case is accepted through the independent no-miss
certificate, has a real finite solver instance, and returns its fallback.
This regression cannot obtain coverage from a pure arm. -/

namespace Yulang.CommonCaseRecordDefaultExamples

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonPatternSourceArmsSolved (SourceArm)

def fallback : CaseDataTerms.Expr Empty := .value (.literal (.int 7))
def arm : SourceArm := ⟨.defaultField 0 fallback (.bind 0) .recordEnd, none, .var 0⟩
def program : CaseDataProgram.Program Empty := ⟨.emptyRecord, [arm]⟩
def binder : Common.Ty := .union .bottom (.base .int)

theorem pure_arms_empty : CommonCaseRecordSourceCoverage.pureArms program.arms = [] := rfl
theorem default_coverage : CommonCaseRecordDefaultCoverage.check Empty.elim [] program.arms = true := rfl

theorem actual_result :
    (ScopedCaseDataProgram.eval Empty.elim [] program).result = .ok (some (.literal (.int 7))) := rfl

theorem exact_empty_width : Common.Subtype Common.exactEmpty Common.emptyRecord :=
  (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl

theorem binder_below_int : Common.Subtype binder (.base .int) :=
  (Common.common_union_is_join _ _ _).mpr ⟨CommonBoundCoalescing.bottom_le _, Common.subtype_refl _⟩

theorem fallback_typed :
    CommonPatternSourceElaboration.DefaultTyped [] [] [] fallback (.base .int) := by
  exact ⟨Common.rowEmpty, .data (.literal ⟨Common.subtype_refl _, Common.rowLe_refl _⟩)⟩

theorem pattern_typed :
    CommonAlignedPatternTyping.Typing (CommonPatternSourceElaboration.DefaultTyped [] []) []
      arm.pattern Common.exactEmpty [(0, binder)] := by
  constructor
  · exact (PatternBindingChecks.check_exact _).mp rfl
  · exact .defaultField (CommonDefaultRequired.optionalPayload_exactEmpty 0 .bottom) fallback_typed .bind
      (.narrow exact_empty_width .recordEnd)

theorem arm_typed :
    CommonPatternSourceArmGeneration.EnvironmentTyping [] [] arm.pattern arm.guard arm.body
      Common.exactEmpty Common.rowEmpty (Comp.pure Common.model (.base .int)) := by
  refine .arm pattern_typed ?_ ?_
  · exact Common.rowLe_refl _
  · exact .var rfl (.mono ⟨binder_below_int, Common.rowLe_refl _⟩)

def assignment : Fin 3 → Comp Common.model
  | ⟨0, _⟩ => Comp.pure Common.model Common.exactEmpty
  | ⟨1, _⟩ => Comp.pure Common.model (.base .unit)
  | _ => Comp.pure Common.model (.base .int)

theorem premises :
    CommonCaseRecordDefaultFamily.Premises [] [] Empty.elim [] program (assignment 0) (assignment 1).2 (assignment 2) := by
  refine ⟨⟨?_, ?_⟩, exact_empty_width, ?_⟩
  · exact .emptyRecord ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  · intro selected member
    have equal : selected = arm := List.mem_singleton.mp member
    subst selected
    exact arm_typed
  · exact (CommonCaseRecordDefaultFamily.coverage_exact Empty.elim [] program.arms).mp default_coverage

theorem real_generated_model :
    (CommonCaseRecordDefaultFamily.principal [] Empty.elim [] program).Holds Common.model assignment :=
  (CommonCaseRecordDefaultFamily.principal_exact [] Empty.elim [] program assignment).mpr premises

theorem real_scheme_instance :
    ∃ scheme ∈ CommonCaseRecordDefaultFamily.solvePremises [] Empty.elim [] program, ∃ parameters : scheme.Parameters,
      CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (CommonCaseRecordDefaultFamily.premises_instances_exact [] Empty.elim [] program assignment).mp premises

end Yulang.CommonCaseRecordDefaultExamples
