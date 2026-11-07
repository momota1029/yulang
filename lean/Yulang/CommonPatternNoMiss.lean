import Yulang.CommonCaseRecordSourceCoverage

/-! Finite certificates that a pattern cannot return a miss. Errors remain
possible, including earlier or-branch/default errors. These are coverage
certificates, not termination or value-typing assertions. -/

namespace Yulang.CommonPatternNoMiss

open CasePatterns (Pattern Observation)
open CaseValues (Value Bindings)
open EvaluationTrace (Logged)

def NoMiss : Except R (Option A) → Prop
  | .error _ => True
  | .ok none => False
  | .ok (some _) => True

inductive EveryValue : Pattern F D → Prop where
  | wildcard : EveryValue .wildcard
  | bind : EveryValue (.bind name)
  | orLeft : EveryValue p → EveryValue (.or p q)
  | orRight : EveryValue q → EveryValue (.or p q)
  | as : EveryValue p → EveryValue (.as p name)

def everyCheck : Pattern F D → Bool
  | .wildcard | .bind _ => true
  | .or p q => everyCheck p || everyCheck q
  | .as p _ => everyCheck p
  | _ => false

theorem everyCheck_exact (pattern : Pattern F D) : everyCheck pattern = true ↔ EveryValue pattern := by
  induction pattern with
  | wildcard => exact ⟨fun _ => .wildcard, fun _ => rfl⟩
  | bind name => exact ⟨fun _ => .bind, fun _ => rfl⟩
  | or p q ihp ihq =>
      simp only [everyCheck, Bool.or_eq_true, ihp, ihq]
      constructor
      · rintro (left | right)
        · exact .orLeft left
        · exact .orRight right
      · intro total
        cases total with
        | orLeft left => exact Or.inl left
        | orRight right => exact Or.inr right
  | as p name ih =>
      simp only [everyCheck, ih]
      exact ⟨EveryValue.as, fun total => by cases total; assumption⟩
  | _ => exact ⟨(fun impossible => by cases impossible), (fun total => by cases total)⟩

theorem andThen_noMiss (first : Observation F E R) (last : Bindings F → Observation F E R)
    (firstTotal : NoMiss first.result) (lastTotal : ∀ prior, NoMiss (last prior).result) :
    NoMiss (ScopedCasePatterns.andThen first last).result := by
  simp only [ScopedCasePatterns.andThen, Logged.bind_result]
  cases observed : first.result with
  | error => trivial
  | ok option =>
      cases option with
      | none => rw [observed] at firstTotal; exact firstTotal.elim
      | some prior =>
          simp only [Except.bind, Logged.bind_result]
          have later := lastTotal prior
          cases result : (last prior).result with
          | error => trivial
          | ok option =>
              cases option with
              | none => rw [result] at later; exact later.elim
              | some more => trivial

theorem EveryValue.run_noMiss (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (total : EveryValue pattern) (environment : Bindings F) (value : Value F) :
    NoMiss (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result := by
  induction total with
  | wildcard | bind => trivial
  | orLeft left ih =>
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error => trivial
      | ok option =>
          cases option with
          | none => rw [observed] at ih; exact ih.elim
          | some => trivial
  | orRight right ih =>
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error => trivial
      | ok option => cases option <;> first | exact ih | trivial
  | as child ih =>
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error => trivial
      | ok option =>
          cases option with
          | none => rw [observed] at ih; exact ih.elim
          | some => trivial

end Yulang.CommonPatternNoMiss
