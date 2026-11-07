import Yulang.ScopedCaseEvaluation

/-! Moving an outer lexical environment from the matcher stack into its
default closure preserves every observation, including failed branches and
errors. The actual callback and all source pattern constructors are retained. -/

namespace Yulang.CommonPatternCapturedEvaluation

open CaseValues EvaluationTrace
open CasePatterns (Pattern)
open CaseEvaluation (Arm Event)

private theorem congr2 (function : A → B → C) (first : a = b) (last : c = d) : function a c = function b d := by
  cases first
  cases last
  rfl

def capture (callback : Bindings F → D → Logged E R (Value F)) (outer : Bindings F)
    (preceding : Bindings F) (code : D) := callback (preceding ++ outer) code

theorem run_capture (floatCheck : F → F → Bool)
    (callback : Bindings F → D → Logged E R (Value F)) (outer : Bindings F)
    (pattern : Pattern F D) (preceding : Bindings F) (value : Value F) :
    ScopedCasePatterns.run floatCheck callback (preceding ++ outer) pattern value =
      ScopedCasePatterns.run floatCheck (capture callback outer) preceding pattern value := by
  induction pattern generalizing preceding value with
  | wildcard | bind | literal | intRange | recordEnd => cases value <;> rfl
  | nil =>
      cases value with
      | list values => cases values <;> rfl
      | literal | pair | record | variant | nominal => rfl
  | pair p q ihp ihq =>
      cases value with
      | pair first last =>
          exact congr2 ScopedCasePatterns.andThen (ihp preceding first)
            (funext fun prior => by simpa only [List.append_assoc] using ihq (prior ++ preceding) last)
      | literal | record | variant | nominal | list => rfl
  | field name p rest ihp ihr =>
      cases value with
      | record fields =>
          simp only [ScopedCasePatterns.run]
          cases lookup name fields with
          | none => rfl
          | some item =>
              exact congr2 ScopedCasePatterns.andThen (ihp preceding item)
                (funext fun prior => by simpa only [List.append_assoc] using ihr (prior ++ preceding) (.record fields))
      | literal | pair | variant | nominal | list => rfl
  | defaultField name fallback p rest ihp ihr =>
      cases value with
      | record fields =>
          simp only [ScopedCasePatterns.run]
          have selected : (match lookup name fields with
              | some value => Logged.ofResult (.ok value)
              | none => callback (preceding ++ outer) fallback) =
            (match lookup name fields with
              | some value => Logged.ofResult (.ok value)
              | none => capture callback outer preceding fallback) := rfl
          apply congr2 Logged.bind selected
          funext item
          exact congr2 ScopedCasePatterns.andThen (ihp preceding item)
            (funext fun prior => by simpa only [List.append_assoc] using ihr (prior ++ preceding) (.record fields))
      | literal | pair | variant | nominal | list => rfl
  | cons p q ihp ihq =>
      cases value with
      | list values =>
          cases values with
          | nil => rfl
          | cons first rest =>
              exact congr2 ScopedCasePatterns.andThen (ihp preceding first)
                (funext fun prior => by simpa only [List.append_assoc] using ihq (prior ++ preceding) (.list rest))
      | literal | pair | record | variant | nominal => rfl
  | snoc p q ihp ihq =>
      cases value with
      | list values =>
          simp only [ScopedCasePatterns.run]
          cases values.reverse with
          | nil => rfl
          | cons last reversed =>
              exact congr2 ScopedCasePatterns.andThen (ihp preceding (.list reversed.reverse))
                (funext fun prior => by simpa only [List.append_assoc] using ihq (prior ++ preceding) last)
      | literal | pair | record | variant | nominal => rfl
  | variant tag p ih =>
      cases value with
      | variant actual payload =>
          simp only [ScopedCasePatterns.run]
          split
          · exact ih preceding payload
          · rfl
      | literal | pair | record | nominal | list => rfl
  | nominal typeId ctorId p ih =>
      cases value with
      | nominal actualType actualCtor payload =>
          simp only [ScopedCasePatterns.run]
          split
          · exact ih preceding payload
          · rfl
      | literal | pair | record | variant | list => rfl
  | or p q ihp ihq =>
      simp only [ScopedCasePatterns.run]
      apply congr2 Logged.bind (ihp preceding value)
      funext result
      cases result with
      | none => exact ihq preceding value
      | some => rfl
  | as p name ih =>
      simp only [ScopedCasePatterns.run]
      exact congr2 Logged.bind (ih preceding value) rfl

theorem testArm_capture (floatCheck : F → F → Bool)
    (callback : Bindings F → D → Logged (Event E) R (Value F)) (outer preceding : Bindings F)
    (guards : G → Bindings F → Logged (Event E) R Bool) (index : Nat) (arm : Arm F D G B) (value : Value F) :
    ScopedCaseEvaluation.testArm floatCheck callback (preceding ++ outer) guards index arm value =
      ScopedCaseEvaluation.testArm floatCheck (capture callback outer) preceding guards index arm value := by
  simp only [ScopedCaseEvaluation.testArm, run_capture]

theorem runArms_capture (floatCheck : F → F → Bool)
    (callback : Bindings F → D → Logged (Event E) R (Value F)) (outer preceding : Bindings F)
    (guards : G → Bindings F → Logged (Event E) R Bool)
    (bodies : B → Bindings F → Logged (Event E) R (Value F))
    (value : Value F) (index : Nat) (arms : List (Arm F D G B)) :
    ScopedCaseEvaluation.runArms floatCheck callback (preceding ++ outer) guards bodies value index arms =
      ScopedCaseEvaluation.runArms floatCheck (capture callback outer) preceding guards bodies value index arms := by
  induction arms generalizing index with
  | nil => rfl
  | cons arm rest ih =>
      simp only [ScopedCaseEvaluation.runArms, testArm_capture]
      congr 2
      funext selected
      cases selected with
      | none => exact ih (index + 1)
      | some => rfl

theorem eval_capture (floatCheck : F → F → Bool)
    (callback : Bindings F → D → Logged (Event E) R (Value F)) (outer preceding : Bindings F)
    (guards : G → Bindings F → Logged (Event E) R Bool)
    (bodies : B → Bindings F → Logged (Event E) R (Value F))
    (subject : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    ScopedCaseEvaluation.eval floatCheck callback (preceding ++ outer) guards bodies subject arms =
      ScopedCaseEvaluation.eval floatCheck (capture callback outer) preceding guards bodies subject arms := by
  simp only [ScopedCaseEvaluation.eval, runArms_capture]

end Yulang.CommonPatternCapturedEvaluation
