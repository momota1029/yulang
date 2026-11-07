import Yulang.CommonPatternAlignedObservations

/-!
# Source or-pattern output alignment at every nested boundary

The recursive matcher retains written-order tests and lazy Q4 defaults.
Only an or-pattern's successful output is reordered to its canonical source
name interface. Default evaluators depend on names rather than list positions.
-/

namespace Yulang.CommonPatternAlignedMatcher

open CaseValues LiteralValues EvaluationTrace
open CasePatterns (Pattern Observation success miss)
open ScopedCasePatterns (andThen)
open PatternBindingChecks (NamesValid)
open CommonPatternBindingAlignment (LookupEq reorder)
open CommonPatternAlignedObservations

def run (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F) :
    Pattern F D → Value F → Observation F E R
  | .wildcard, _ => success []
  | .bind name, value => success [(name, value)]
  | .literal expected, .literal actual =>
      if matchCheck floatCheck expected actual then success [] else miss
  | .literal _, _ => miss
  | .intRange lower upper, .literal actual =>
      if intRangeCheck lower upper actual then success [] else miss
  | .intRange _ _, _ => miss
  | .pair p q, .pair first last => andThen (run floatCheck defaultEval environment p first)
      (fun prior => run floatCheck defaultEval (prior ++ environment) q last)
  | .pair _ _, _ => miss
  | .recordEnd, .record _ => success []
  | .recordEnd, _ => miss
  | .field name p rest, .record fields =>
      match lookup name fields with
      | none => miss
      | some value => andThen (run floatCheck defaultEval environment p value)
          (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields))
  | .field _ _ _, _ => miss
  | .defaultField name fallback p rest, .record fields =>
      let selected := match lookup name fields with
        | some value => Logged.ofResult (.ok value)
        | none => defaultEval environment fallback
      selected.bind fun value => andThen (run floatCheck defaultEval environment p value)
        (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields))
  | .defaultField _ _ _ _, _ => miss
  | .nil, .list [] => success []
  | .nil, _ => miss
  | .cons p q, .list (first :: rest) => andThen (run floatCheck defaultEval environment p first)
      (fun prior => run floatCheck defaultEval (prior ++ environment) q (.list rest))
  | .cons _ _, _ => miss
  | .snoc p q, .list values =>
      match values.reverse with
      | [] => miss
      | last :: reversed => andThen (run floatCheck defaultEval environment p (.list reversed.reverse))
          (fun prior => run floatCheck defaultEval (prior ++ environment) q last)
  | .snoc _ _, _ => miss
  | .variant tag p, .variant name value =>
      if tag = name then run floatCheck defaultEval environment p value else miss
  | .variant _ _, _ => miss
  | .nominal typeId ctorId p, .nominal actualType actualCtor value =>
      if typeId = actualType ∧ ctorId = actualCtor then run floatCheck defaultEval environment p value else miss
  | .nominal _ _ _, _ => miss
  | .or p q, value => alignResult p.names <|
      (run floatCheck defaultEval environment p value).bind fun result =>
        match result with
        | some values => success values
        | none => run floatCheck defaultEval environment q value
  | .as p name, value => (run floatCheck defaultEval environment p value).bind fun result =>
      match result with
      | none => miss
      | some values => success ((name, value) :: values)

def DefaultInvariant (defaultEval : Bindings F → D → Logged E R (Value F)) : Prop :=
  ∀ first last, LookupEq first last → ∀ code, defaultEval first code = defaultEval last code

theorem equivalent_refl (observed : Observation F E R) : Equivalent observed observed := by
  refine ⟨rfl, ?_⟩
  cases observed.result with
  | error => exact .error
  | ok option =>
      cases option with
      | none => exact .ok .miss
      | some => exact .ok (.hit (fun _ => rfl))

/-- Arbitrary source-valid patterns, values, name-equivalent incoming
environments, and name-invariant default evaluation, including every error
and event type. The whole trace/error/miss is preserved; successful bindings
have the same lookup at every name. No positional-typing or success premise. -/
theorem run_equivalent (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (defaults : DefaultInvariant defaultEval)
    (pattern : Pattern F D) (valid : NamesValid pattern)
    (first last : Bindings F) (same : LookupEq first last) (value : Value F) :
    Equivalent (run floatCheck defaultEval first pattern value)
      (ScopedCasePatterns.run floatCheck defaultEval last pattern value) := by
  induction pattern generalizing first last value with
  | wildcard | bind => exact equivalent_refl _
  | literal | intRange | recordEnd => cases value <;> exact equivalent_refl _
  | nil =>
      cases value with
      | list values => cases values <;> exact equivalent_refl _
      | _ => exact equivalent_miss
  | pair p q ihp ihq =>
      cases valid with
      | pair vp vq apart =>
          cases value <;> first
          | (apply andThen_equivalent (ihp vp first last same _)
             intro a b related
             exact ihq vq _ _ (lookup_eq_append related same) _)
          | exact equivalent_miss
  | field name p rest ihp ihr =>
      cases valid with
      | field vp vr apart =>
          cases value with
          | record fields =>
              simp only [run, ScopedCasePatterns.run]
              cases selected : lookup name fields with
              | none => exact equivalent_miss
              | some item =>
                  apply andThen_equivalent (ihp vp first last same item)
                  intro a b related
                  exact ihr vr _ _ (lookup_eq_append related same) _
          | _ => exact equivalent_miss
  | defaultField name fallback p rest ihp ihr =>
      cases valid with
      | defaultField vp vr apart =>
          cases value with
          | record fields =>
              simp only [run, ScopedCasePatterns.run]
              have selected :
                  (match lookup name fields with
                    | some value => Logged.ofResult (.ok value)
                    | none => defaultEval first fallback) =
                  (match lookup name fields with
                    | some value => Logged.ofResult (.ok value)
                    | none => defaultEval last fallback) := by
                cases lookup name fields with
                | some => rfl
                | none => exact defaults first last same fallback
              apply logged_bind (relation := Eq)
                (by rw [selected]; exact logged_equal _)
              intro a b equal
              subst b
              apply andThen_equivalent (ihp vp first last same a)
              intro prior prior' related
              exact ihr vr _ _ (lookup_eq_append related same) _
          | _ => exact equivalent_miss
  | cons p q ihp ihq =>
      cases valid with
      | cons vp vq apart =>
          cases value with
          | list values =>
              cases values with
              | nil => exact equivalent_miss
              | cons head tail =>
                  apply andThen_equivalent (ihp vp first last same head)
                  intro a b related
                  exact ihq vq _ _ (lookup_eq_append related same) (.list tail)
          | _ => exact equivalent_miss
  | snoc p q ihp ihq =>
      cases valid with
      | snoc vp vq apart =>
          cases value with
          | list values =>
              simp only [run, ScopedCasePatterns.run]
              cases selected : values.reverse with
              | nil => exact equivalent_miss
              | cons head tail =>
                  apply andThen_equivalent (ihp vp first last same (.list tail.reverse))
                  intro a b related
                  exact ihq vq _ _ (lookup_eq_append related same) head
          | _ => exact equivalent_miss
  | variant tag p ih =>
      cases valid with
      | variant vp =>
          cases value <;> first
          | (simp only [run, ScopedCasePatterns.run]
             split
             · exact ih vp first last same _
             · exact equivalent_miss)
          | exact equivalent_miss
  | nominal typeId ctorId p ih =>
      cases valid with
      | nominal vp =>
          cases value <;> first
          | (simp only [run, ScopedCasePatterns.run]
             split
             · exact ih vp first last same _
             · exact equivalent_miss)
          | exact equivalent_miss
  | or p q ihp ihq =>
      have wholeValid := valid
      cases valid with
      | or vp vq names =>
          apply alignResult_equivalent (names := p.names)
          · apply logged_bind (ihp vp first last same value)
            intro a b related
            cases related with
            | miss => exact ihq vq first last same value
            | hit related => exact equivalent_success related
          · intro output matched name member
            exact ((CommonPatternMatchPaths.run_binding_path floatCheck defaultEval (.or p q)
              last value output matched).names wholeValid name).mp member
  | as p name ih =>
      cases valid with
      | as vp fresh =>
          apply logged_bind (ih vp first last same value)
          intro a b related
          cases related with
          | miss => exact equivalent_miss
          | hit related => exact equivalent_success (related.cons name value)

theorem data_defaults_invariant : DefaultInvariant (F := F) CaseDataTerms.defaultEval :=
  fun first last same code => CommonPatternBindingAlignment.data_eval_lookup_eq code first last same

theorem default_present (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (name : Nat) (fallback : D) (p rest : Pattern F D) (fields : Bindings F) (value : Value F)
    (present : lookup name fields = some value) :
    run floatCheck defaultEval environment (.defaultField name fallback p rest) (.record fields) =
      andThen (run floatCheck defaultEval environment p value)
        (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields)) := by
  simp [run, present, Logged.ofResult, Logged.bind]

theorem default_absent (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (name : Nat) (fallback : D) (p rest : Pattern F D) (fields : Bindings F)
    (absent : lookup name fields = none) :
    run floatCheck defaultEval environment (.defaultField name fallback p rest) (.record fields) =
      (defaultEval environment fallback).bind fun value =>
        andThen (run floatCheck defaultEval environment p value)
          (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields)) := by
  simp [run, absent]

end Yulang.CommonPatternAlignedMatcher
