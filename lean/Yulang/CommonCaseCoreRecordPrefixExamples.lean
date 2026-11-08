import Yulang.CommonCaseCoreRecordPrefixSolved

/-! The combined Core record family is inhabited by a default-only arm.
The default is an actual Core literal and its result reaches the actual Core
body through the generated monomorphic binder. No pure arm can provide the
coverage certificate. This witnesses the stated bounded premise factor;
the unresolved source-presence and principal-row contracts remain separate. -/

namespace Yulang.CommonCaseCoreRecordPrefixExamples

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonCaseCoreBoundedGeneration (Arm runtimeArm)

def fallback : Required.Term := .literal (.int 7)
def arm : Arm := (.defaultField 0 fallback (.bind 0) .recordEnd, none, .var 0)
def subject : Required.Term := .emptyRecord
def binder : Common.Ty := .union .bottom (.base .int)

theorem pure_arms_empty : CommonCaseRecordSourceCoverage.pureArms [runtimeArm arm] = [] := rfl
theorem default_coverage :
    CommonCaseRecordDefaultCoverage.check Empty.elim [] [runtimeArm arm] = true := rfl

theorem exact_empty_width : Common.Subtype Common.exactEmpty Common.emptyRecord :=
  (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl

theorem binder_below_int : Common.Subtype binder (.base .int) :=
  (Common.common_union_is_join _ _ _).mpr ⟨CommonBoundCoalescing.bottom_le _, Common.subtype_refl _⟩

theorem fallback_typed :
    CommonPatternCoreBoundedDefaults.DefaultTyped [] Common.rowEmpty [] fallback (.base .int) :=
  ⟨Common.rowEmpty, .literal ⟨Common.subtype_refl _, Common.rowLe_refl _⟩, Common.rowLe_refl _⟩

theorem pattern_typed :
    CommonAlignedPatternTyping.Typing (CommonPatternCoreBoundedDefaults.DefaultTyped [] Common.rowEmpty) []
      arm.1 Common.exactEmpty [(0, binder)] := by
  constructor
  · exact (PatternBindingChecks.check_exact _).mp rfl
  · exact .defaultField (CommonDefaultRequired.optionalPayload_exactEmpty 0 .bottom) fallback_typed .bind
      (.narrow exact_empty_width .recordEnd)

theorem arm_typed :
    CommonCaseCoreBoundedGeneration.EnvironmentTyping [] arm.1 arm.2.1 arm.2.2
      Common.exactEmpty (.base .int) Common.rowEmpty := by
  refine .arm pattern_typed ?_ ?_
  · exact Common.rowLe_refl _
  · exact .var rfl (.mono ⟨binder_below_int, Common.rowLe_refl _⟩)

def assignment : Fin 3 → Comp Common.model
  | ⟨0, _⟩ => Comp.pure Common.model Common.exactEmpty
  | ⟨1, _⟩ => Comp.pure Common.model (.base .int)
  | _ => Comp.pure Common.model (.base .unit)

theorem premises :
    CommonCaseCoreRecordPrefixSolved.Premises [] Empty.elim [] subject [arm]
      (assignment 0).1 (assignment 1).1 (assignment 2).2 := by
  refine ⟨⟨?_, ?_⟩, exact_empty_width, ?_⟩
  · exact .emptyRecord ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  · intro selected member
    have same : selected = arm := List.mem_singleton.mp member
    subst selected
    exact arm_typed
  · exact (CommonCaseCoreRecordPrefixSolved.coverage_exact Empty.elim [] [arm]).mp default_coverage

theorem real_generated_model :
    (CommonCaseCoreRecordPrefixSolved.principal Empty.elim [] subject [arm]).Holds Common.model assignment :=
  (CommonCaseCoreRecordPrefixSolved.principal_exact Empty.elim [] subject [arm] assignment).mpr premises

/-- The actual finite solver returns a scheme and an unrestricted parameter
instance representing the concrete input, result and empty row above. -/
theorem real_scheme_instance :
    ∃ scheme ∈ CommonCaseCoreRecordPrefixSolved.solvePremises Empty.elim [] subject [arm],
      ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (CommonCaseCoreRecordPrefixSolved.premises_instances_exact Empty.elim [] subject [arm] assignment).mp premises

end Yulang.CommonCaseCoreRecordPrefixExamples
