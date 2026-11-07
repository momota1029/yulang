import Yulang.CommonPatternBindingAlignment
import Yulang.ScopedCasePatterns
import Yulang.PatternBindingChecks

/-! A successful raw matcher produces one actual source binding path, even
when defaults/guards may fail. This is independent of positional typing. -/

namespace Yulang.CommonPatternMatchPaths

open CaseValues CasePatterns EvaluationTrace PatternBindingChecks
open CommonPatternBindingAlignment (reorder LookupEq)

theorem andThen_success (first : Observation F E R) (last : Bindings F → Observation F E R)
    (returned : (ScopedCasePatterns.andThen first last).result = .ok (some output)) :
    ∃ left right, first.result = .ok (some left) ∧ (last left).result = .ok (some right) ∧ output = left ++ right := by
  simp only [ScopedCasePatterns.andThen, Logged.bind_result] at returned
  cases firstResult : first.result with
  | error error => simp [Except.bind] at returned
  | ok option =>
      rw [firstResult] at returned
      cases option with
      | none => cases returned
      | some left =>
          simp only [Except.bind, Logged.bind_result] at returned
          cases lastResult : (last left).result with
          | error error => simp [lastResult] at returned
          | ok option =>
              rw [lastResult] at returned
              cases option with
              | none => cases returned
              | some right =>
                  have equal : left ++ right = output := by
                    simpa only [Except.bind, success, Logged.ofResult, Except.ok.injEq, Option.some.injEq] using returned
                  exact ⟨left, right, rfl, lastResult, equal.symm⟩

theorem run_binding_path (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (environment : Bindings F) (value : Value F) (output : Bindings F)
    (matched : (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some output)) :
    BindingPath pattern (output.map Prod.fst) := by
  induction pattern generalizing environment value output with
  | wildcard =>
      have equal : output = [] := by simpa only [ScopedCasePatterns.run, success, Logged.ofResult,
        Except.ok.injEq, Option.some.injEq] using matched.symm
      subst output; exact .wildcard
  | bind name =>
      have equal : output = [(name, value)] := by simpa only [ScopedCasePatterns.run, success, Logged.ofResult,
        Except.ok.injEq, Option.some.injEq] using matched.symm
      subst output; exact .bind
  | literal expected =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · have equal : output = [] := by simpa [success, Logged.ofResult] using matched.symm
           subst output; exact .literal
         · cases matched)
      | cases matched
  | intRange lower upper =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · have equal : output = [] := by simpa [success, Logged.ofResult] using matched.symm
           subst output; exact .intRange
         · cases matched)
      | cases matched
  | pair p q ihp ihq =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
         rw [List.map_append]
         exact .pair (ihp _ _ _ first) (ihq _ _ _ last))
      | cases matched
  | recordEnd =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (have equal : output = [] := by simpa [success, Logged.ofResult] using matched.symm
         subst output; exact .recordEnd)
      | cases matched
  | field name p rest ihp ihr =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · cases matched
         · obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
           rw [List.map_append]
           exact .field (ihp _ _ _ first) (ihr _ _ _ last))
      | cases matched
  | defaultField name fallback p rest ihp ihr =>
      cases value with
      | record fields =>
          cases found : CaseValues.lookup name fields with
          | some item =>
              rw [ScopedCasePatterns.default_present _ _ _ _ _ _ _ _ _ found] at matched
              obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
              rw [List.map_append]
              exact .defaultField (ihp _ _ _ first) (ihr _ _ _ last)
          | none =>
              rw [ScopedCasePatterns.default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result] at matched
              cases evaluated : (defaultEval environment fallback).result with
              | error error => rw [evaluated] at matched; cases matched
              | ok item =>
                  rw [evaluated] at matched
                  obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
                  rw [List.map_append]
                  exact .defaultField (ihp _ _ _ first) (ihr _ _ _ last)
      | _ => simp only [ScopedCasePatterns.run] at matched; cases matched
  | nil =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · have equal : output = [] := by simpa [success, Logged.ofResult] using matched.symm
           subst output; exact .nil
         · cases matched)
      | (have equal : output = [] := by simpa [success, Logged.ofResult] using matched.symm
         subst output; exact .nil)
      | cases matched
  | cons p q ihp ihq =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
           rw [List.map_append]
           exact .cons (ihp _ _ _ first) (ihq _ _ _ last)
         · cases matched)
      | cases matched
  | snoc p q ihp ihq =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · cases matched
         · obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
           rw [List.map_append]
           exact .snoc (ihp _ _ _ first) (ihq _ _ _ last))
      | cases matched
  | variant tag p ih =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · exact .variant (ih _ _ _ matched)
         · cases matched)
      | cases matched
  | nominal typeId ctorId p ih =>
      cases value <;> simp only [ScopedCasePatterns.run] at matched
      all_goals first
      | (split at matched
         · exact .nominal (ih _ _ _ matched)
         · cases matched)
      | cases matched
  | or p q ihp ihq =>
      simp only [ScopedCasePatterns.run, Logged.bind_result] at matched
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment p value).result with
      | error error => rw [observed] at matched; cases matched
      | ok option =>
          rw [observed] at matched
          cases option with
          | none => exact .orRight (ihq _ _ _ matched)
          | some prior =>
              have equal : output = prior := by simpa [success, Logged.ofResult, Except.bind] using matched.symm
              subst output
              exact .orLeft (ihp _ _ _ observed)
  | as p name ih =>
      simp only [ScopedCasePatterns.run, Logged.bind_result] at matched
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment p value).result with
      | error error => rw [observed] at matched; cases matched
      | ok option =>
          rw [observed] at matched
          cases option with
          | none => cases matched
          | some prior =>
              have equal : output = (name, value) :: prior := by simpa [success, Logged.ofResult, Except.bind] using matched.symm
              subst output
              exact .as (ih _ _ _ observed)

end Yulang.CommonPatternMatchPaths
