import Yulang.CommonPatternAlignedMatcher

/-! The canonical ordered matcher is polymorphic in computations. No
termination or successful-return assumption is imposed on default code.
`Ops` is an explicit interface, without global instances or assumed monad
laws. The old finite logged matcher is proved to be its exact specialization.
An interpretation by source computations is a separate obligation. -/

namespace Yulang.CommonPatternComputations

open CaseValues LiteralValues
open CasePatterns (Pattern)
open CommonPatternBindingAlignment (reorder)
open EvaluationTrace (Logged)

structure Ops (M : Type → Type) where
  ret : {A : Type} → A → M A
  bind : {A B : Type} → M A → (A → M B) → M B

def andThen (ops : Ops M) (first : M (Option (Bindings F)))
    (next : Bindings F → M (Option (Bindings F))) : M (Option (Bindings F)) :=
  ops.bind first fun result => match result with
    | none => ops.ret none
    | some prior => ops.bind (next prior) fun result => match result with
      | none => ops.ret none
      | some more => ops.ret (some (prior ++ more))

def align (ops : Ops M) (names : List Nat) (first : M (Option (Bindings F))) : M (Option (Bindings F)) :=
  ops.bind first fun result => ops.ret (result.map (reorder names))

def run (ops : Ops M) (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → M (Value F)) (environment : Bindings F) :
    Pattern F D → Value F → M (Option (Bindings F))
  | .wildcard, _ => ops.ret (some [])
  | .bind name, value => ops.ret (some [(name, value)])
  | .literal expected, .literal actual =>
      if matchCheck floatCheck expected actual then ops.ret (some []) else ops.ret none
  | .literal _, _ => ops.ret none
  | .intRange lower upper, .literal actual =>
      if intRangeCheck lower upper actual then ops.ret (some []) else ops.ret none
  | .intRange _ _, _ => ops.ret none
  | .pair p q, .pair first last => andThen ops (run ops floatCheck defaultEval environment p first)
      (fun prior => run ops floatCheck defaultEval (prior ++ environment) q last)
  | .pair _ _, _ => ops.ret none
  | .recordEnd, .record _ => ops.ret (some [])
  | .recordEnd, _ => ops.ret none
  | .field name p rest, .record fields =>
      match lookup name fields with
      | none => ops.ret none
      | some value => andThen ops (run ops floatCheck defaultEval environment p value)
          (fun prior => run ops floatCheck defaultEval (prior ++ environment) rest (.record fields))
  | .field _ _ _, _ => ops.ret none
  | .defaultField name fallback p rest, .record fields =>
      let selected := match lookup name fields with
        | some value => ops.ret value
        | none => defaultEval environment fallback
      ops.bind selected fun value => andThen ops (run ops floatCheck defaultEval environment p value)
        (fun prior => run ops floatCheck defaultEval (prior ++ environment) rest (.record fields))
  | .defaultField _ _ _ _, _ => ops.ret none
  | .nil, .list [] => ops.ret (some [])
  | .nil, _ => ops.ret none
  | .cons p q, .list (first :: rest) => andThen ops (run ops floatCheck defaultEval environment p first)
      (fun prior => run ops floatCheck defaultEval (prior ++ environment) q (.list rest))
  | .cons _ _, _ => ops.ret none
  | .snoc p q, .list values =>
      match values.reverse with
      | [] => ops.ret none
      | last :: reversed => andThen ops (run ops floatCheck defaultEval environment p (.list reversed.reverse))
          (fun prior => run ops floatCheck defaultEval (prior ++ environment) q last)
  | .snoc _ _ , _ => ops.ret none
  | .variant tag p, .variant name value =>
      if tag = name then run ops floatCheck defaultEval environment p value else ops.ret none
  | .variant _ _, _ => ops.ret none
  | .nominal typeId ctorId p, .nominal actualType actualCtor value =>
      if typeId = actualType ∧ ctorId = actualCtor then run ops floatCheck defaultEval environment p value else ops.ret none
  | .nominal _ _ _, _ => ops.ret none
  | .or p q, value => align ops p.names <|
      ops.bind (run ops floatCheck defaultEval environment p value) fun result => match result with
        | some values => ops.ret (some values)
        | none => run ops floatCheck defaultEval environment q value
  | .as p name, value => ops.bind (run ops floatCheck defaultEval environment p value) fun result => match result with
      | none => ops.ret none
      | some values => ops.ret (some ((name, value) :: values))

def loggedOps (E R : Type) : Ops (Logged E R) :=
  ⟨fun value => Logged.ofResult (.ok value), Logged.bind⟩

@[simp] theorem ret_logged (value : A) :
    (loggedOps E R).ret value = Logged.ofResult (.ok value) := rfl

@[simp] theorem bind_logged (first : Logged E R A) (next : A → Logged E R B) :
    (loggedOps E R).bind first next = first.bind next := rfl

theorem andThen_logged (first : CasePatterns.Observation F E R)
    (next : Bindings F → CasePatterns.Observation F E R) :
    andThen (loggedOps E R) first next = ScopedCasePatterns.andThen first next := rfl

theorem align_logged (names : List Nat) (first : CasePatterns.Observation F E R) :
    align (loggedOps E R) names first = CommonPatternAlignedObservations.alignResult names first := by
  cases first with
  | mk events result => cases result <;> simp [align, loggedOps, Logged.bind,
      Logged.ofResult, CommonPatternAlignedObservations.alignResult, Except.map]

/-- Literal equality of the whole computation, including traces and errors,
for every default callback, pattern, incoming scope, and real value. -/
theorem run_logged (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (environment : Bindings F) (value : Value F) :
    run (loggedOps E R) floatCheck defaultEval environment pattern value =
      CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value := by
  induction pattern generalizing environment value with
  | wildcard | bind => rfl
  | literal | intRange | recordEnd => cases value <;> rfl
  | pair p q ihp ihq =>
      cases value <;> simp [run, CommonPatternAlignedMatcher.run, andThen_logged, ihp, ihq, CasePatterns.miss]
  | field name p rest ihp ihr =>
      cases value with
      | record fields =>
          simp only [run, CommonPatternAlignedMatcher.run]
          cases lookup name fields <;> simp only [andThen_logged, ihp, ihr] <;> rfl
      | _ => rfl
  | defaultField name fallback p rest ihp ihr =>
      cases value <;> simp [run, CommonPatternAlignedMatcher.run, CasePatterns.miss]
      simp only [andThen_logged, ihp, ihr]
      rfl
  | nil => cases value <;> first | rfl | (rename_i values; cases values <;> rfl)
  | cons p q ihp ihq =>
      cases value with
      | list values => cases values <;> simp only [run, CommonPatternAlignedMatcher.run, andThen_logged, ihp, ihq] <;> rfl
      | _ => rfl
  | snoc p q ihp ihq =>
      cases value with
      | list values =>
          simp only [run, CommonPatternAlignedMatcher.run]
          cases values.reverse <;> simp only [andThen_logged, ihp, ihq] <;> rfl
      | _ => rfl
  | variant tag p ih => cases value <;> simp [run, CommonPatternAlignedMatcher.run, ih, CasePatterns.miss]
  | nominal typeId ctorId p ih => cases value <;> simp [run, CommonPatternAlignedMatcher.run, ih, CasePatterns.miss]
  | or p q ihp ihq =>
      simp only [run, CommonPatternAlignedMatcher.run, align_logged, ihp, ihq, bind_logged, ret_logged, CasePatterns.success]
      rfl
  | as p name ih =>
      simp only [run, CommonPatternAlignedMatcher.run, ih, bind_logged, ret_logged, CasePatterns.success, CasePatterns.miss]
      rfl

end Yulang.CommonPatternComputations
