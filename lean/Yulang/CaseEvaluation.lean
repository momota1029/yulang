import Yulang.CasePatternSafety

/-!
# Ordered case evaluation with guards

The case node owns the pattern/guard/body order. Leaf expression evaluation is
an explicit interface, so a source compiler cannot replace a failed match by a
fabricated result or evaluate every arm eagerly. The independent typing of
leaves is parameterized; the generic theorem assumes its soundness contract,
not a successful runtime result for each particular arm.
-/

namespace Yulang.CaseEvaluation

open CaseValues CasePatterns EvaluationTrace

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

inductive Event (Source : Type) where
  | source : Source → Event Source
  | scrutinee
  | arm : Nat → Event Source
  | guard : Nat → Event Source
  | body : Nat → Event Source
  deriving Repr, DecidableEq

structure Arm (F D G B : Type) where
  pattern : Pattern F D
  guard : Option G
  body : B
  deriving Repr

def testArm (floatCheck : F → F → Bool)
    (defaultEval : D → Logged (Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (index : Nat) (arm : Arm F D G B) (value : Value F) :
    Observation F (Event E) R :=
  (CasePatterns.run floatCheck defaultEval arm.pattern value).bind fun matched =>
    match matched with
    | none => miss
    | some bindings => match arm.guard with
      | none => success bindings
      | some guard => Logged.prepend [.guard index] <|
          (guardEval guard bindings).bind fun accepted =>
            if accepted then success bindings else miss

def runArms (floatCheck : F → F → Bool)
    (defaultEval : D → Logged (Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (value : Value F) (index : Nat) : List (Arm F D G B) → Logged (Event E) R (Option (Value F))
  | [] => Logged.ofResult (.ok none)
  | arm :: rest => Logged.prepend [.arm index] <|
      (testArm floatCheck defaultEval guardEval index arm value).bind fun selected =>
        match selected with
        | none => runArms floatCheck defaultEval guardEval bodyEval value (index + 1) rest
        | some bindings => Logged.prepend [.body index] <|
            (bodyEval arm.body bindings).bind fun result => Logged.ofResult (.ok (some result))

def eval (floatCheck : F → F → Bool)
    (defaultEval : D → Logged (Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (scrutinee : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    Logged (Event E) R (Option (Value F)) :=
  Logged.prepend [.scrutinee] <| scrutinee.bind fun value =>
    runArms floatCheck defaultEval guardEval bodyEval value 0 arms

def GuardSound (GuardTyped : G → List (Nat × Ty F) → Prop)
    (guardEval : G → Bindings F → Logged (Event E) R Bool) : Prop :=
  ∀ guard types, GuardTyped guard types → ∀ bindings, BindingsHold types bindings →
    ∃ result, (guardEval guard bindings).result = .ok result

def BodySound (BodyTyped : B → List (Nat × Ty F) → Ty F → Prop)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F)) : Prop :=
  ∀ body types target, BodyTyped body types target → ∀ bindings, BindingsHold types bindings →
    ∃ result, (bodyEval body bindings).result = .ok result ∧ target result

inductive ArmTyping (DefaultTyped : D → Ty F → Prop)
    (GuardTyped : G → List (Nat × Ty F) → Prop)
    (BodyTyped : B → List (Nat × Ty F) → Ty F → Prop) :
    Arm F D G B → Ty F → Ty F → Prop where
  | arm (pattern : CasePatterns.Typing DefaultTyped arm.pattern input bindings)
      (guard : ∀ code, arm.guard = some code → GuardTyped code bindings)
      (body : BodyTyped arm.body bindings target) : ArmTyping DefaultTyped GuardTyped BodyTyped arm input target

def ResultHolds (target : Ty F) : Except R (Option (Value F)) → Prop
  | .error _ => False
  | .ok none => True
  | .ok (some value) => target value

theorem testArm_typed (floatCheck : F → F → Bool)
    (defaultEval : D → Logged (Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (defaults : DefaultSound DefaultTyped defaultEval) (guards : GuardSound GuardTyped guardEval)
    {arm : Arm F D G B}
    (patternTyped : CasePatterns.Typing DefaultTyped arm.pattern input bindings)
    (guardTyped : ∀ code, arm.guard = some code → GuardTyped code bindings)
    (value : Value F) (valid : input value) (index : Nat) :
    Holds bindings (testArm floatCheck defaultEval guardEval index arm value).result := by
  have safe := typing_matches floatCheck defaultEval defaults patternTyped value valid
  simp only [testArm, Logged.bind_result]
  cases observed : (CasePatterns.run floatCheck defaultEval arm.pattern value).result with
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
    (defaultEval : D → Logged (Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (guards : GuardSound GuardTyped guardEval)
    (bodies : BodySound BodyTyped bodyEval)
    (arms : List (Arm F D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped arm input target)
    (value : Value F) (valid : input value) (index : Nat) :
    ResultHolds target (runArms floatCheck defaultEval guardEval bodyEval value index arms).result := by
  induction arms generalizing index with
  | nil => trivial
  | cons arm rest ih =>
      obtain ⟨patternTyped, guardTyped, bodyTyped⟩ := typed arm (by simp)
      have safe := testArm_typed floatCheck defaultEval guardEval defaults guards
        patternTyped guardTyped value valid index
      simp only [runArms, Logged.prepend_result, Logged.bind_result]
      cases observed : (testArm floatCheck defaultEval guardEval index arm value).result with
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
    (defaultEval : D → Logged (Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (guards : GuardSound GuardTyped guardEval)
    (bodies : BodySound BodyTyped bodyEval)
    (arms : List (Arm F D G B))
    (typed : ∀ arm ∈ arms, ArmTyping DefaultTyped GuardTyped BodyTyped arm input target)
    (value : Value F) (valid : input value)
    (covered : ∃ arm ∈ arms, arm.guard = none ∧ ∃ bindings,
      (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings))
    (index : Nat) :
    ∃ result, (runArms floatCheck defaultEval guardEval bodyEval value index arms).result = .ok (some result)
      ∧ target result := by
  induction arms generalizing index with
  | nil => obtain ⟨arm, member, _⟩ := covered; cases member
  | cons arm rest ih =>
      obtain ⟨patternTyped, guardTyped, bodyTyped⟩ := typed arm (by simp)
      have safe := testArm_typed floatCheck defaultEval guardEval defaults guards
        patternTyped guardTyped value valid index
      simp only [runArms, Logged.prepend_result, Logged.bind_result]
      cases observed : (testArm floatCheck defaultEval guardEval index arm value).result with
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

end Yulang.CaseEvaluation
