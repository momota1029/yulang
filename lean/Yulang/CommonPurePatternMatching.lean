import Yulang.CoreScopedPatterns

/-! A callback-free finite matcher for patterns with no default code.
It retains every source constructor, list direction, nominal identity and
literal payload. The exactness theorem compares complete real observations,
not only Boolean acceptance. No Common list/nominal typing rule is assumed. -/

namespace Yulang.CommonPurePatternMatching

open CaseValues LiteralValues EvaluationTrace
open CasePatterns (Pattern)

def combine (first last : Option (Bindings F)) : Option (Bindings F) :=
  first.bind fun left => last.map (left ++ ·)

def bindings (floatCheck : F → F → Bool) : Pattern F Empty → Value F → Option (Bindings F)
  | .wildcard, _ => some []
  | .bind name, value => some [(name, value)]
  | .literal expected, .literal actual => if matchCheck floatCheck expected actual then some [] else none
  | .intRange lower upper, .literal actual => if intRangeCheck lower upper actual then some [] else none
  | .pair p q, .pair first last => combine (bindings floatCheck p first) (bindings floatCheck q last)
  | .recordEnd, .record _ => some []
  | .field name p rest, .record fields =>
      (lookup name fields).bind fun value => combine (bindings floatCheck p value) (bindings floatCheck rest (.record fields))
  | .defaultField _ impossible _ _, _ => impossible.elim
  | .nil, .list [] => some []
  | .cons p rest, .list (first :: last) => combine (bindings floatCheck p first) (bindings floatCheck rest (.list last))
  | .snoc initial p, .list values => match values.reverse with
      | [] => none
      | last :: reversed => combine (bindings floatCheck initial (.list reversed.reverse)) (bindings floatCheck p last)
  | .variant tag p, .variant actual value => if tag = actual then bindings floatCheck p value else none
  | .nominal typeId ctorId p, .nominal actualType actualCtor value =>
      if typeId = actualType ∧ ctorId = actualCtor then bindings floatCheck p value else none
  | .or p q, value => (bindings floatCheck p value).orElse (fun _ => bindings floatCheck q value)
  | .as p name, value => (bindings floatCheck p value).map ((name, value) :: ·)
  | _, _ => none

theorem combine_isSome (first last : Option (Bindings F)) :
    (combine first last).isSome = (first.isSome && last.isSome) := by cases first <;> cases last <;> rfl

private theorem andThen_pure (first last : Option (Bindings F)) :
    CasePatterns.andThen (E := E) (R := R) (Logged.ofResult (.ok first)) (fun _ => Logged.ofResult (.ok last)) =
      Logged.ofResult (.ok (combine first last)) := by cases first <;> cases last <;> rfl

theorem run_unscoped_exact (floatCheck : F → F → Bool) (pattern : Pattern F Empty) (value : Value F) :
    CasePatterns.run floatCheck (Empty.elim : Empty → Logged E R (Value F)) pattern value =
      Logged.ofResult (.ok (bindings floatCheck pattern value)) := by
  induction pattern generalizing value with
  | wildcard | bind => rfl
  | literal expected =>
      cases value <;> simp only [CasePatterns.run, bindings] <;> try rfl
      split <;> rfl
  | intRange lower upper =>
      cases value <;> simp only [CasePatterns.run, bindings] <;> try rfl
      split <;> rfl
  | pair p q ihp ihq =>
      cases value <;> simp only [CasePatterns.run, bindings] <;> try rfl
      rw [ihp, ihq]
      exact andThen_pure _ _
  | recordEnd => cases value <;> rfl
  | field name p rest ihp ihr =>
      cases value <;> simp only [CasePatterns.run, bindings] <;> try rfl
      rename_i fields
      cases found : lookup name fields with
      | none => rfl
      | some item =>
          simp only [Option.bind_some, ihp, ihr]
          exact andThen_pure _ _
  | defaultField name impossible p rest ihp ihr => exact impossible.elim
  | nil =>
      cases value <;> try rfl
      rename_i values
      cases values <;> rfl
  | cons p rest ihp ihr =>
      cases value <;> try rfl
      rename_i values
      cases values with
      | nil => rfl
      | cons first last =>
          simp only [CasePatterns.run, bindings, ihp, ihr]
          exact andThen_pure _ _
  | snoc initial p ihi ihp =>
      cases value <;> try rfl
      rename_i values
      simp only [CasePatterns.run, bindings]
      cases values.reverse with
      | nil => rfl
      | cons last reversed =>
          simp only [ihi, ihp]
          exact andThen_pure _ _
  | variant tag p ih =>
      cases value <;> simp only [CasePatterns.run, bindings] <;> try rfl
      split
      · exact ih _
      · rfl
  | nominal typeId ctorId p ih =>
      cases value <;> simp only [CasePatterns.run, bindings] <;> try rfl
      split
      · exact ih _
      · rfl
  | or p q ihp ihq =>
      simp only [CasePatterns.run, bindings, ihp]
      cases bindings floatCheck p value <;> simp [Logged.bind, Logged.ofResult, ihq, CasePatterns.success]
  | as p name ih =>
      simp only [CasePatterns.run, bindings, ih]
      cases bindings floatCheck p value <;> simp [Logged.bind, Logged.ofResult, CasePatterns.success, CasePatterns.miss]

/-- All real callbacks and captured environments are irrelevant because a
Pattern F Empty has no executable default. All binding identities and the
entire empty trace are retained, including list/nominal/float matching. -/
theorem run_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → Empty → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F Empty) (value : Value F) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern value =
      Logged.ofResult (.ok (bindings floatCheck pattern value)) := by
  have unique : defaultEval = fun _ => Empty.elim := by
    funext actual impossible
    exact impossible.elim
  rw [unique, ScopedCasePatterns.run_constant_defaults]
  exact run_unscoped_exact floatCheck pattern value

/-- Mapping actual default code commutes with the unmodified matcher,
including all Q4 environments, misses, errors and prior observations. -/
theorem run_map (floatCheck : F → F → Bool) (mapCode : D → D')
    (defaultEval : Bindings F → D' → Logged E R (Value F))
    (environment : Bindings F) (pattern : Pattern F D) (value : Value F) :
    ScopedCasePatterns.run floatCheck defaultEval environment (Core.Patterns.map mapCode pattern) value =
      ScopedCasePatterns.run floatCheck (fun actual code => defaultEval actual (mapCode code)) environment pattern value := by
  induction pattern generalizing environment value <;> cases value <;>
    (try simp_all [Core.Patterns.map, ScopedCasePatterns.run, ScopedCasePatterns.andThen]) <;> try rfl
  all_goals
    rename_i values
    cases values <;> simp_all [ScopedCasePatterns.run, ScopedCasePatterns.andThen] <;> rfl

theorem run_embed_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F Empty) (value : Value F) :
    ScopedCasePatterns.run floatCheck defaultEval environment (Core.Patterns.map Empty.elim pattern) value =
      Logged.ofResult (.ok (bindings floatCheck pattern value)) := by
  rw [run_map]
  exact run_exact floatCheck _ environment pattern value

end Yulang.CommonPurePatternMatching
