import Yulang.CommonPurePatternPrefixNoMiss
import Yulang.CommonCaseFinitePrefixes
import Yulang.CommonCaseRecordDefaultCoverage

/-! Record coverage excludes completed all-arm mismatch for the actual
ordered finite-prefix case interpreter. Earlier defaults and guards may
diverge or fail, and a selected body may diverge or fail. None of those
observations is counted as a successful match or a terminating value. -/

namespace Yulang.CommonCasePrefixCoverage

open CaseValues (Value Bindings)
open CaseEvaluation (Arm)
open CommonPatternFinitePrefixes (Computation Observation Safe Bind ret ops)
open CommonPatternPrefixNoMiss (Returns NoMiss returns_bind bind_noMiss ret_some_noMiss)
open CommonCaseComputations (Visit testArm runArms eval)
open CommonCaseFinitePrefixes (Prepend visits)
open CommonCaseRecordCells (Specification Domain)

theorem returns_prepend (visit : Visit) (computation : Computation E R A) (value : A) :
    Returns (Prepend visit computation) value ↔ Returns computation value := by
  constructor
  · rintro ⟨trace, present⟩
    have completed (observed : Observation E R A) (within : Prepend visit computation observed) :
        observed.result = some (.ok value) → Returns computation value := by
      cases within with
      | pending => intro impossible; cases impossible
      | next original present =>
          intro same
          refine ⟨original.trace, ?_⟩
          cases original with
          | mk events result =>
              simp only at same
              cases same
              exact present
    exact completed _ present rfl
  · rintro ⟨trace, present⟩
    exact ⟨visit.event :: trace, .next ⟨trace, some (.ok value)⟩ present⟩

theorem prepend_noMiss (visit : Visit) (computation : Computation E R (Option A))
    (noMiss : NoMiss computation) : NoMiss (Prepend visit computation) :=
  fun returned => noMiss ((returns_prepend visit computation none).mp returned)

theorem unguarded_noMiss (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Computation E R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Computation E R Bool) (index : Nat) (arm : Arm F D G B)
    (unguarded : arm.guard = none) (value : Value F)
    (pattern : NoMiss (CommonPatternComputations.run (ops E R) floatCheck defaultEval environment arm.pattern value)) :
    NoMiss (testArm (ops E R) (visits E R) floatCheck defaultEval environment guardEval index arm value) := by
  apply bind_noMiss
  intro option returned
  cases option with
  | none => exact False.elim (pattern returned)
  | some bindings =>
      simp only [unguarded]
      exact ret_some_noMiss _

/-- An unguarded no-miss witness may occur anywhere in the original list.
Every earlier arm is still tried in order; an error or unfinished callback
does not force evaluation of a later arm. -/
theorem witness_noMiss (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Computation E R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Computation E R Bool)
    (bodyEval : B → Bindings F → Computation E R (Value F))
    (value : Value F) (index : Nat) (arms : List (Arm F D G B))
    (witness : Arm F D G B) (member : witness ∈ arms) (unguarded : witness.guard = none)
    (pattern : NoMiss (CommonPatternComputations.run (ops E R) floatCheck defaultEval environment witness.pattern value)) :
    NoMiss (runArms (ops E R) (visits E R) floatCheck defaultEval environment guardEval bodyEval value index arms) := by
  induction arms generalizing index with
  | nil => cases member
  | cons arm rest ih =>
      apply prepend_noMiss
      apply bind_noMiss
      intro option returned
      cases option with
      | none =>
          rcases List.mem_cons.mp member with rfl | later
          · exact False.elim ((unguarded_noMiss floatCheck defaultEval environment guardEval index witness unguarded value pattern) returned)
          · exact ih (index + 1) later
      | some bindings =>
          apply prepend_noMiss
          apply bind_noMiss
          intro output _
          exact ret_some_noMiss output

/-- The unchanged finite pure/default record checker supplies the witness
internally. Callback completeness, success, determinism and termination are
not hypotheses; all their represented finite observations are admitted. -/
theorem covered_noMiss (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Computation E R (Value Empty)) (environment : Bindings Empty)
    (guardEval : G → Bindings Empty → Computation E R Bool)
    (bodyEval : B → Bindings Empty → Computation E R (Value Empty))
    (specification : Specification) (arms : List (Arm Empty D G B))
    (coverage : CommonCaseRecordDefaultCoverage.check floatCheck specification arms = true)
    (fields : Bindings Empty) (valid : Domain specification fields) (index : Nat) :
    NoMiss (runArms (ops E R) (visits E R) floatCheck defaultEval environment guardEval bodyEval (.record fields) index arms) := by
  rcases (CommonCaseRecordDefaultCoverage.check_exact floatCheck specification arms).mp coverage with pure | certified
  · obtain ⟨arm, member, unguarded, noMiss⟩ :=
      CommonPurePatternPrefixNoMiss.joint_record_witness floatCheck defaultEval environment specification arms pure fields valid
    exact witness_noMiss floatCheck defaultEval environment guardEval bodyEval (.record fields) index arms arm member unguarded noMiss
  · obtain ⟨arm, member, unguarded, total⟩ := certified
    exact witness_noMiss floatCheck defaultEval environment guardEval bodyEval (.record fields) index arms arm member unguarded
      (CommonPatternPrefixNoMiss.record_noMiss floatCheck defaultEval total fields valid environment)

theorem eval_noMiss (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Computation E R (Value Empty)) (environment : Bindings Empty)
    (guardEval : G → Bindings Empty → Computation E R Bool)
    (bodyEval : B → Bindings Empty → Computation E R (Value Empty))
    (specification : Specification) (arms : List (Arm Empty D G B))
    (coverage : CommonCaseRecordDefaultCoverage.check floatCheck specification arms = true)
    (scrutinee : Computation E R (Value Empty))
    (domain : ∀ value, Returns scrutinee value → ∃ fields, value = .record fields ∧ Domain specification fields) :
    NoMiss (eval (ops E R) (visits E R) floatCheck defaultEval environment guardEval bodyEval scrutinee arms) := by
  apply prepend_noMiss
  apply bind_noMiss
  intro value returned
  obtain ⟨fields, rfl, valid⟩ := domain value returned
  exact covered_noMiss floatCheck defaultEval environment guardEval bodyEval specification arms coverage fields valid 0

def SuccessfulResult (target : Common.Ty) : Option (Value Empty) → Prop
  | none => False
  | some value => CommonPatternTyping.valueAt target value

/-- Combine row/type safety with coverage, without asserting a return.
Every completed successful observation now contains a typed selected value;
unfinished prefixes and declared errors retain the original row bound. -/
theorem safe_selected_result (source : E → Common.Row) (failure : R → Common.Row)
    (computation : Computation E R (Option (Value Empty))) (target : Common.Ty) (cap : Common.Row)
    (safe : Safe source failure computation (CommonCaseComputationSafety.ResultHolds target) cap)
    (noMiss : NoMiss computation) : Safe source failure computation (SuccessfulResult target) cap := by
  intro observed present
  have valid := safe observed present
  refine ⟨valid.1, ?_⟩
  intro output returned
  cases output with
  | none =>
      apply noMiss
      refine ⟨observed.trace, ?_⟩
      cases observed with
      | mk trace result =>
          simp only at returned
          cases returned
          exact present
  | some value => exact valid.2 (some value) returned

end Yulang.CommonCasePrefixCoverage
