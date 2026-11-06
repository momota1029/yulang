import Yulang.ScopedCasePatternSafety
import Yulang.CaseEvaluation

/-!
# Ordered case arms with scope-aware defaults

This evaluator keeps the existing arm representation and leaf observations.
Pattern defaults see the current lexical environment and preceding pattern
bindings. Guards and bodies receive the completed bindings; a false guard
continues with the next arm and never retries an or alternative.
-/

namespace Yulang.ScopedCaseEvaluation

open CaseValues EvaluationTrace ScopedCasePatterns
open CasePatterns (Pattern Observation success miss Holds)
open CaseEvaluation (Event Arm GuardSound BodySound ResultHolds)

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

def testArm (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (index : Nat) (arm : Arm F D G B) (value : Value F) :
    Observation F (Event E) R :=
  (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).bind fun matched =>
    match matched with
    | none => miss
    | some bindings => match arm.guard with
      | none => success bindings
      | some guard => Logged.prepend [.guard index] <|
          (guardEval guard bindings).bind fun accepted =>
            if accepted then success bindings else miss

def runArms (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (value : Value F) (index : Nat) : List (Arm F D G B) → Logged (Event E) R (Option (Value F))
  | [] => Logged.ofResult (.ok none)
  | arm :: rest => Logged.prepend [.arm index] <|
      (testArm floatCheck defaultEval environment guardEval index arm value).bind fun selected =>
        match selected with
        | none => runArms floatCheck defaultEval environment guardEval bodyEval value (index + 1) rest
        | some bindings => Logged.prepend [.body index] <|
            (bodyEval arm.body bindings).bind fun result => Logged.ofResult (.ok (some result))

def eval (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    Logged (Event E) R (Option (Value F)) :=
  Logged.prepend [.scrutinee] <| scrutinee.bind fun value =>
    runArms floatCheck defaultEval environment guardEval bodyEval value 0 arms

inductive ArmTyping (DefaultTyped : List (Nat × Ty F) → D → Ty F → Prop)
    (GuardTyped : G → List (Nat × Ty F) → Prop)
    (BodyTyped : B → List (Nat × Ty F) → Ty F → Prop) :
    List (Nat × Ty F) → Arm F D G B → Ty F → Ty F → Prop where
  | arm (pattern : ScopedCasePatterns.Typing DefaultTyped types arm.pattern input bindings)
      (guard : ∀ code, arm.guard = some code → GuardTyped code bindings)
      (body : BodyTyped arm.body bindings target) : ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target

theorem testArm_typed (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (defaults : DefaultSound DefaultTyped defaultEval) (guards : GuardSound GuardTyped guardEval)
    {arm : Arm F D G B}
    (patternTyped : ScopedCasePatterns.Typing DefaultTyped types arm.pattern input bindings)
    (guardTyped : ∀ code, arm.guard = some code → GuardTyped code bindings)
    (value : Value F) (valid : input value) (index : Nat)
    (environmentValid : BindingsHold types environment) :
    Holds bindings (testArm floatCheck defaultEval environment guardEval index arm value).result := by
  have safe := typing_matches floatCheck defaultEval defaults patternTyped environment environmentValid value valid
  simp only [testArm, Logged.bind_result]
  cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result with
  | error error => rw [observed] at safe; cases safe
  | ok option =>
      rw [observed] at safe
      cases option with
      | none => trivial
      | some matched =>
          cases hg : arm.guard with
          | none => exact safe
          | some code =>
              obtain ⟨accepted, ran⟩ := guards code bindings (guardTyped code hg) matched safe
              simp only [except_bind_ok, Logged.prepend_result, Logged.bind_result, ran]
              cases accepted <;> first | trivial | exact safe

theorem runArms_typed (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (guards : GuardSound GuardTyped guardEval)
    (bodies : BodySound BodyTyped bodyEval)
    (arms : List (Arm F D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target)
    (value : Value F) (valid : input value) (index : Nat)
    (environmentValid : BindingsHold types environment) :
    ResultHolds target (runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result := by
  induction arms generalizing index with
  | nil => trivial
  | cons arm rest ih =>
      obtain ⟨patternTyped, guardTyped, bodyTyped⟩ := typed arm (by simp)
      have safe := testArm_typed floatCheck defaultEval environment guardEval defaults guards
        patternTyped guardTyped value valid index environmentValid
      simp only [runArms, Logged.prepend_result, Logged.bind_result]
      cases observed : (testArm floatCheck defaultEval environment guardEval index arm value).result with
      | error error => rw [observed] at safe; cases safe
      | ok option =>
          rw [observed] at safe
          cases option with
          | none => exact ih (fun a member => typed a (by simp [member])) (index + 1)
          | some matched =>
              obtain ⟨result, ran, resultValid⟩ := bodies _ _ _ bodyTyped matched safe
              simpa [Logged.bind_result, ran, Logged.ofResult, ResultHolds] using resultValid

/-- A successful unguarded pattern suffices for eventual selection. Earlier
typed arms may select first; a guard may fail, but cannot supply coverage. -/
theorem runArms_progress (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (guards : GuardSound GuardTyped guardEval)
    (bodies : BodySound BodyTyped bodyEval)
    (arms : List (Arm F D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target)
    (value : Value F) (valid : input value)
    (covered : ∃ arm ∈ arms, arm.guard = none ∧ ∃ bindings,
      (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result = .ok (some bindings))
    (index : Nat) (environmentValid : BindingsHold types environment) :
    ∃ result, (runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result = .ok (some result)
      ∧ target result := by
  induction arms generalizing index with
  | nil => obtain ⟨arm, member, _⟩ := covered; cases member
  | cons arm rest ih =>
      obtain ⟨patternTyped, guardTyped, bodyTyped⟩ := typed arm (by simp)
      have safe := testArm_typed floatCheck defaultEval environment guardEval defaults guards
        patternTyped guardTyped value valid index environmentValid
      simp only [runArms, Logged.prepend_result, Logged.bind_result]
      cases observed : (testArm floatCheck defaultEval environment guardEval index arm value).result with
      | error error => rw [observed] at safe; cases safe
      | ok option =>
          rw [observed] at safe
          cases option with
          | some matched =>
              obtain ⟨result, ran, resultValid⟩ := bodies _ _ _ bodyTyped matched safe
              exact ⟨result, by simp [Logged.bind_result, ran, Logged.ofResult], resultValid⟩
          | none =>
              apply ih (fun a member => typed a (by simp [member])) ?_ (index + 1)
              obtain ⟨coveredArm, member, unguarded, bindings, matched⟩ := covered
              rcases List.mem_cons.mp member with same | member
              · subst coveredArm
                simp [testArm, Logged.bind_result, matched, unguarded, success, Logged.ofResult] at observed
              · exact ⟨coveredArm, member, unguarded, bindings, matched⟩

end Yulang.ScopedCaseEvaluation
