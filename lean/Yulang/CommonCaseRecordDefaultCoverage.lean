import Yulang.CommonRecordNoMiss
import Yulang.CommonCaseRecordEnvironmentFamily

/-! Combine joint pure-record cells with independent no-miss certificates
for executable defaults. Original arm order and all callback observations
remain operationally unchanged. This is a sound coverage extension, not a
complete decision procedure for every default-dependent pattern matrix. -/

namespace Yulang.CommonCaseRecordDefaultCoverage

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event ResultHolds)
open CommonCaseRecordCells (Specification Domain)
open CommonPatternNoMiss (NoMiss)

def certifiedCheck (specification : Specification) (arms : List (Arm Empty D G B)) : Bool :=
  arms.any fun arm => !arm.guard.isSome && CommonRecordNoMiss.check specification arm.pattern

theorem certifiedCheck_exact (specification : Specification) (arms : List (Arm Empty D G B)) :
    certifiedCheck specification arms = true ↔
      ∃ arm ∈ arms, arm.guard = none ∧ CommonRecordNoMiss.Total specification arm.pattern := by
  simp only [certifiedCheck, List.any_eq_true, Bool.and_eq_true, CommonRecordNoMiss.check_exact]
  apply exists_congr
  intro arm
  apply and_congr_right
  intro member
  cases arm.guard <;> simp

def check (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List (Arm Empty D G B)) : Bool :=
  CommonCaseRecordSourceCoverage.check floatCheck specification arms || certifiedCheck specification arms

theorem check_exact (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List (Arm Empty D G B)) :
    check floatCheck specification arms = true ↔
      CommonCaseRecordSourceCoverage.check floatCheck specification arms = true ∨
        ∃ arm ∈ arms, arm.guard = none ∧ CommonRecordNoMiss.Total specification arm.pattern := by
  simp only [check, Bool.or_eq_true, certifiedCheck_exact]

theorem unguarded_test_result (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool) (index : Nat) (arm : Arm F D G B)
    (unguarded : arm.guard = none) (value : Value F) :
    (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result =
      (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result := by
  simp only [ScopedCaseEvaluation.testArm, Logged.bind_result]
  cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result with
  | error => rfl
  | ok option => cases option <;> simp [Except.bind, unguarded, CasePatterns.success, CasePatterns.miss, Logged.ofResult]

theorem allMiss_unguarded_pattern_miss (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (misses : CommonCaseOrderedPaths.AllMiss floatCheck defaultEval environment guardEval value index arms) :
    ∀ arm ∈ arms, arm.guard = none →
      (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result = .ok none := by
  induction misses with
  | nil => intro arm member; cases member
  | cons tested later ih =>
      intro arm member unguarded
      rcases List.mem_cons.mp member with rfl | tail
      · have result := congrArg Logged.result tested.observation
        rwa [unguarded_test_result floatCheck defaultEval environment guardEval _ arm unguarded value] at result
      · exact ih arm tail unguarded

/-- Arbitrary erroring/effectful finite callbacks. A reached certified arm
may error, but cannot miss; consequently the whole original ordered case
cannot report all-arm mismatch. No default-success premise is used. -/
theorem covered_not_unmatched (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged (Event E) R (Value Empty)) (environment : Bindings Empty)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (bodyEval : B → Bindings Empty → Logged (Event E) R (Value Empty))
    (specification : Specification) (arms : List (Arm Empty D G B))
    (coverage : check floatCheck specification arms = true) (fields : Bindings Empty) (valid : Domain specification fields) (index : Nat) :
    (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval (.record fields) index arms).result ≠ .ok none := by
  rcases (check_exact floatCheck specification arms).mp coverage with pure | certified
  · exact CommonCaseRecordSourceCoverage.covered_not_unmatched floatCheck defaultEval environment guardEval bodyEval
      specification arms pure fields valid index
  · intro unmatched
    have misses := (CommonCaseOrderedPaths.runArms_unmatched_exact floatCheck defaultEval environment guardEval bodyEval
      (.record fields) index arms).mp unmatched
    obtain ⟨arm, member, unguarded, total⟩ := certified
    have noMiss := total.run_noMiss floatCheck defaultEval fields valid environment
    have missed := allMiss_unguarded_pattern_miss floatCheck defaultEval environment guardEval misses arm member unguarded
    rw [missed] at noMiss
    exact noMiss

open Core
open PresenceGeneration (Comp)
open CommonPatternDataSafety (EnvironmentHolds)
open CommonPatternSourceArmGeneration (EnvironmentTyping)
open CommonPatternSourceArmsSolved (SourceArm)
open CommonPatternTyping (valueAt)

def Coverage (floatCheck : Empty → Empty → Bool) (specification : CommonCaseRecordReadout.Specification) (arms : List SourceArm) : Prop :=
  CommonCaseRecordEnvironmentFamily.Coverage floatCheck specification arms ∨
    ∃ arm ∈ arms, arm.guard = none ∧ CommonRecordNoMiss.Total (CommonCaseRecordReadout.shapes specification) arm.pattern

theorem source_coverage_exact (floatCheck : Empty → Empty → Bool) (specification : CommonCaseRecordReadout.Specification)
    (arms : List SourceArm) : check floatCheck (CommonCaseRecordReadout.shapes specification) arms = true ↔ Coverage floatCheck specification arms := by
  simp only [check_exact, Coverage, CommonCaseRecordEnvironmentFamily.coverage_exact]

theorem record_runArms_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (arms : List SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (specification : CommonCaseRecordReadout.Specification)
    (inputRecord : Common.Subtype input (CommonCaseRecordReadout.type specification))
    (floatCheck : Empty → Empty → Bool) (coverage : check floatCheck (CommonCaseRecordReadout.shapes specification) arms = true)
    (value : CommonData.Value) (valid : valueAt input value) (index : Nat) :
    ∃ output, (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
      (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result = .ok (some output) ∧
      valueAt result.1 output := by
  have safe := CommonPatternConcreteCaseTotal.actual_runArms_safe outer arms typed floatCheck value valid index
  obtain ⟨fields, rfl, domain⟩ := CommonCaseRecordReadout.readout specification value _ valid inputRecord
  have selected := covered_not_unmatched floatCheck CaseDataTerms.defaultEval actualOuter
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) _ arms coverage fields domain index
  cases observed : (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) (.record fields) index arms).result with
  | error => rw [observed] at safe; cases safe
  | ok option =>
      cases option with
      | none => exact False.elim (selected observed)
      | some output => exact ⟨output, rfl, by simpa only [observed, ResultHolds] using safe⟩

theorem record_program_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (program : CaseDataProgram.Program Empty) (subject : Comp Common.model)
    (subjectTyped : CommonSyntax.Typing Common.model environment (Data.embed outerNames program.scrutinee) subject)
    (typed : ∀ arm ∈ program.arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body subject.1 guardRow result)
    (specification : CommonCaseRecordReadout.Specification)
    (inputRecord : Common.Subtype subject.1 (CommonCaseRecordReadout.type specification))
    (floatCheck : Empty → Empty → Bool)
    (coverage : check floatCheck (CommonCaseRecordReadout.shapes specification) program.arms = true) :
    ∃ output, (ScopedCaseDataProgram.eval floatCheck actualOuter program).result = .ok (some output) ∧ valueAt result.1 output := by
  obtain ⟨value, evaluated, safe⟩ := CommonPatternDataSafety.typing_evaluates program.scrutinee outerNames environment
    actualOuter subject outer subjectTyped
  have valueTyped := CommonPatternLookup.typing_change_result safe (Comp.pure Common.model subject.1) (Common.subtype_refl _)
  obtain ⟨output, selected, outputType⟩ := record_runArms_progress outer program.arms typed specification inputRecord floatCheck coverage value valueTyped 0
  exact ⟨output, by simpa only [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.prepend_result,
    Logged.bind_result, evaluated, Except.bind] using selected, outputType⟩

end Yulang.CommonCaseRecordDefaultCoverage
