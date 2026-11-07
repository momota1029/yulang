import Yulang.CommonCaseRecordCoverage
import Yulang.CommonPurePatternErasure
import Yulang.CommonCaseIntegerOrdered

/-! Pure record coverage is extracted from arbitrary actual source arm lists.
Default-containing arms remain in source order and may execute; they are not
counted as coverage witnesses by this particular checker. -/

namespace Yulang.CommonCaseRecordSourceCoverage

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event ResultHolds)
open CommonCaseRecordCells (Specification Domain)
open CommonPurePatternErasure (erase)

def pureArm (arm : Arm F D G B) : Option (Arm F Empty G B) :=
  (erase arm.pattern).map fun pattern => ⟨pattern, arm.guard, arm.body⟩

def pureArms (arms : List (Arm F D G B)) : List (Arm F Empty G B) := arms.filterMap pureArm

theorem mem_pureArms (arms : List (Arm F D G B)) (pure : Arm F Empty G B) :
    pure ∈ pureArms arms ↔ ∃ original ∈ arms, ∃ pattern,
      erase original.pattern = some pattern ∧ pure = ⟨pattern, original.guard, original.body⟩ := by
  constructor
  · intro member
    obtain ⟨original, included, compiled⟩ := List.mem_filterMap.mp member
    obtain ⟨pattern, compiled, same⟩ := (CommonPurePatternErasure.mapped_some _ _ _).mp compiled
    exact ⟨original, included, pattern, compiled, same.symm⟩
  · rintro ⟨original, included, pattern, compiled, rfl⟩
    exact List.mem_filterMap.mpr ⟨original, included, by simp only [pureArm, compiled, Option.map_some]⟩

def check (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List (Arm Empty D G B)) : Bool :=
  CommonCaseRecordCoverage.check floatCheck specification (pureArms arms)

/-- Exactness for the stated pure-witness factor, with arbitrary actual
default callbacks. Erasure eligibility is part of the conclusion, not an
assumption that all source arms lack defaults. -/
theorem check_matches_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (specification : Specification) (arms : List (Arm Empty D G B)) :
    check floatCheck specification arms = true ↔ ∀ fields, Domain specification fields →
      ∃ arm ∈ arms, arm.guard = none ∧ ∃ pure, erase arm.pattern = some pure ∧ ∃ returned,
        (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern (.record fields)).result = .ok (some returned) := by
  rw [check, CommonCaseRecordCoverage.check_matches_exact floatCheck (fun _ => Empty.elim) environment]
  constructor
  · intro covered fields valid
    obtain ⟨pure, member, unguarded, returned, matched⟩ := covered fields valid
    obtain ⟨original, included, pattern, compiled, rfl⟩ := (mem_pureArms arms pure).mp member
    have same := (CommonPurePatternErasure.actual_match_exact floatCheck defaultEval environment original.pattern pattern compiled (.record fields)).trans
      (CommonPurePatternMatching.run_exact floatCheck (fun _ => Empty.elim) environment pattern (.record fields)).symm
    exact ⟨original, included, unguarded, pattern, compiled, returned, (congrArg Logged.result same).trans matched⟩
  · intro covered fields valid
    obtain ⟨original, member, unguarded, pattern, compiled, returned, matched⟩ := covered fields valid
    have same := (CommonPurePatternErasure.actual_match_exact floatCheck defaultEval environment original.pattern pattern compiled (.record fields)).trans
      (CommonPurePatternMatching.run_exact floatCheck (fun _ => Empty.elim) environment pattern (.record fields)).symm
    exact ⟨⟨pattern, original.guard, original.body⟩,
      (mem_pureArms arms _).mpr ⟨original, member, pattern, compiled, rfl⟩, unguarded, returned,
      (congrArg Logged.result same).symm.trans matched⟩

theorem covered_not_unmatched (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged (Event E) R (Value Empty)) (environment : Bindings Empty)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (bodyEval : B → Bindings Empty → Logged (Event E) R (Value Empty))
    (specification : Specification) (arms : List (Arm Empty D G B))
    (coverage : check floatCheck specification arms = true) (fields : Bindings Empty) (valid : Domain specification fields) (index : Nat) :
    (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval (.record fields) index arms).result ≠ .ok none := by
  intro unmatched
  have misses := (CommonCaseOrderedPaths.runArms_unmatched_exact floatCheck defaultEval environment guardEval bodyEval
    (.record fields) index arms).mp unmatched
  obtain ⟨arm, member, unguarded, pure, compiled, returned, matched⟩ :=
    (check_matches_exact floatCheck defaultEval environment specification arms).mp coverage fields valid
  exact CommonCaseIntegerOrdered.allMiss_no_unguarded_match floatCheck defaultEval environment guardEval
    misses arm member unguarded returned matched

open Core
open PresenceGeneration (Comp)
open CommonPatternDataSafety (EnvironmentHolds)
open CommonPatternSourceArmGeneration (EnvironmentTyping)
open CommonPatternSourceArmsSolved (SourceArm)
open CommonPatternTyping (valueAt)

/-- All finite source data arms are typed, including executable defaults.
The checker supplies a pure coverage witness internally; earlier arms still
execute in the original order and the source callbacks discharge safety. -/
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
  obtain ⟨output, selected, outputType⟩ := record_runArms_progress outer program.arms typed specification inputRecord floatCheck coverage
    value valueTyped 0
  exact ⟨output, by simpa only [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.prepend_result,
    Logged.bind_result, evaluated, Except.bind] using selected, outputType⟩

end Yulang.CommonCaseRecordSourceCoverage
