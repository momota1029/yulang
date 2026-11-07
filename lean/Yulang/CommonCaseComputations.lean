import Yulang.CommonPatternComputations
import Yulang.CommonAlignedCaseEvaluation

/-! The ordered case evaluator over arbitrary computations. Administrative
visits remain explicit, so the Logged specialization preserves literal traces
as well as errors and returns. Neither guards nor defaults need terminate. -/

namespace Yulang.CommonCaseComputations

open CommonPatternComputations (Ops loggedOps ret_logged bind_logged run_logged)
open CaseValues (Value Bindings)
open CaseEvaluation (Arm Event)
open EvaluationTrace (Logged)

inductive Visit where
  | scrutinee
  | arm (index : Nat)
  | guard (index : Nat)
  | body (index : Nat)

def Visit.event : Visit → Event E
  | .scrutinee => .scrutinee
  | .arm index => .arm index
  | .guard index => .guard index
  | .body index => .body index

structure Visits (M : Type → Type) where
  prepend : {A : Type} → Visit → M A → M A

def testArm (ops : Ops M) (visits : Visits M) (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → M (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → M Bool) (index : Nat) (arm : Arm F D G B) (value : Value F) :
    M (Option (Bindings F)) :=
  ops.bind (CommonPatternComputations.run ops floatCheck defaultEval environment arm.pattern value) fun matched =>
    match matched with
    | none => ops.ret none
    | some bindings => match arm.guard with
      | none => ops.ret (some bindings)
      | some guard => visits.prepend (.guard index) <|
          ops.bind (guardEval guard bindings) fun accepted =>
            if accepted then ops.ret (some bindings) else ops.ret none

def runArms (ops : Ops M) (visits : Visits M) (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → M (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → M Bool) (bodyEval : B → Bindings F → M (Value F))
    (value : Value F) (index : Nat) : List (Arm F D G B) → M (Option (Value F))
  | [] => ops.ret none
  | arm :: rest => visits.prepend (.arm index) <|
      ops.bind (testArm ops visits floatCheck defaultEval environment guardEval index arm value) fun selected =>
        match selected with
        | none => runArms ops visits floatCheck defaultEval environment guardEval bodyEval value (index + 1) rest
        | some bindings => visits.prepend (.body index) <|
            ops.bind (bodyEval arm.body bindings) fun result => ops.ret (some result)

def eval (ops : Ops M) (visits : Visits M) (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → M (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → M Bool) (bodyEval : B → Bindings F → M (Value F))
    (scrutinee : M (Value F)) (arms : List (Arm F D G B)) : M (Option (Value F)) :=
  visits.prepend .scrutinee <| ops.bind scrutinee fun value =>
    runArms ops visits floatCheck defaultEval environment guardEval bodyEval value 0 arms

def loggedVisits (E R : Type) : Visits (Logged (Event E) R) :=
  ⟨fun visit computation => Logged.prepend [visit.event] computation⟩

@[simp] theorem prepend_logged (visit : Visit) (computation : Logged (Event E) R A) :
    (loggedVisits E R).prepend visit computation = computation.prepend [visit.event] := rfl

theorem testArm_logged (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (index : Nat) (arm : Arm F D G B) (value : Value F) :
    testArm (loggedOps (Event E) R) (loggedVisits E R) floatCheck defaultEval environment guardEval index arm value =
      CommonAlignedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value := by
  simp only [testArm, CommonAlignedCaseEvaluation.testArm, run_logged, bind_logged]
  apply congrArg
  funext matched
  cases matched with
  | none => rfl
  | some bindings => cases arm.guard <;> rfl

/-- The complete finite arm traversal keeps first-match order and every
administrative/source visit, even when a callback returns an error. -/
theorem runArms_logged (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (value : Value F) (index : Nat) (arms : List (Arm F D G B)) :
    runArms (loggedOps (Event E) R) (loggedVisits E R) floatCheck defaultEval environment guardEval bodyEval value index arms =
      CommonAlignedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms := by
  induction arms generalizing index with
  | nil => rfl
  | cons arm rest ih =>
      simp only [runArms, CommonAlignedCaseEvaluation.runArms, testArm_logged, prepend_logged, bind_logged]
      apply congrArg (Logged.prepend [Event.arm index])
      apply congrArg
      funext selected
      cases selected with
      | none => exact ih (index + 1)
      | some bindings => rfl

theorem eval_logged (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    eval (loggedOps (Event E) R) (loggedVisits E R) floatCheck defaultEval environment guardEval bodyEval scrutinee arms =
      CommonAlignedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval scrutinee arms := by
  simp only [eval, CommonAlignedCaseEvaluation.eval, prepend_logged, bind_logged, runArms_logged]
  rfl

end Yulang.CommonCaseComputations
