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
  | error error => rw [firstResult] at returned; cases returned
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
      cases value with
      | list values =>
          cases values with
          | nil =>
              have equal : output = [] := by simpa [ScopedCasePatterns.run, success, Logged.ofResult] using matched.symm
              subst output; exact .nil
          | cons => cases matched
      | _ => cases matched
  | cons p q ihp ihq =>
      cases value with
      | list values =>
          cases values with
          | nil => cases matched
          | cons first tail =>
              obtain ⟨left, right, first, last, rfl⟩ := andThen_success _ _ matched
              rw [List.map_append]
              exact .cons (ihp _ _ _ first) (ihq _ _ _ last)
      | _ => cases matched
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

/-- A source-valid raw match can be aligned to the source interface's names.
Every original lookup is preserved, even if a right or branch wrote the
same binders in a different order. No default success contract is needed. -/
theorem matched_alignment (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (valid : NamesValid pattern) (environment : Bindings F) (value : Value F) (output : Bindings F)
    (matched : (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some output)) :
    (reorder pattern.names output).map Prod.fst = pattern.names ∧
      LookupEq (reorder pattern.names output) output := by
  have names := (run_binding_path floatCheck defaultEval pattern environment value output matched).names valid
  exact ⟨CommonPatternBindingAlignment.reorder_names _ _ (fun name member => (names name).mpr member),
    CommonPatternBindingAlignment.reorder_lookup_eq _ _ (fun name member => (names name).mp member)⟩

/-- The next concrete named default/guard/body sees exactly the same values
after interface alignment, including errors and the entire evaluation trace.
This is local to a completed matching part, so it can also apply at nested
or boundaries rather than only at the final arm output. -/
theorem following_data_eval_alignment (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (valid : NamesValid pattern) (environment : Bindings F) (value : Value F) (output : Bindings F)
    (matched : (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some output))
    (next : CaseDataTerms.Expr F) :
    CaseDataTerms.eval (reorder pattern.names output ++ environment) next =
      CaseDataTerms.eval (output ++ environment) next :=
  CommonPatternBindingAlignment.data_eval_lookup_eq next _ _
    ((matched_alignment floatCheck defaultEval pattern valid environment value output matched).2.append environment)

theorem canonical_binding_path (pattern : Pattern F D) : BindingPath pattern pattern.names := by
  induction pattern with
  | wildcard => exact .wildcard
  | bind => exact .bind
  | literal => exact .literal
  | intRange => exact .intRange
  | pair p q ihp ihq => exact .pair ihp ihq
  | recordEnd => exact .recordEnd
  | field name p q ihp ihq => exact .field ihp ihq
  | defaultField name fallback p q ihp ihq => exact .defaultField ihp ihq
  | nil => exact .nil
  | cons p q ihp ihq => exact .cons ihp ihq
  | snoc p q ihp ihq => exact .snoc ihp ihq
  | variant tag p ih => exact .variant ih
  | nominal typeId ctorId p ih => exact .nominal ih
  | or p q ihp ihq => exact .orLeft ihp
  | as p name ih => exact .as ih

theorem source_names_nodup (pattern : Pattern F D) (valid : NamesValid pattern) : pattern.names.Nodup :=
  valid.path_nodup (canonical_binding_path pattern)

end Yulang.CommonPatternMatchPaths
