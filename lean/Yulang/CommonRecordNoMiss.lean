import Yulang.CommonPatternNoMiss

/-! Independent sufficient certificates for record patterns that cannot
miss, including missing-field defaults. Error observations are admitted.
This is not a completeness claim for all source coverage matrices. -/

namespace Yulang.CommonRecordNoMiss

open CaseValues (Value Bindings lookup)
open CasePatterns (Pattern)
open EvaluationTrace (Logged)
open CommonCaseBaseCells (Shape InShape)
open CommonCaseRecordCells (Specification Domain)
open CommonPatternNoMiss (NoMiss EveryValue everyCheck)

def PayloadTotal (shape : Shape) (pattern : Pattern Empty D) : Prop :=
  ∀ value, InShape shape value → CommonCaseBaseMatching.accepts pattern value = true

def payloadCheck (shape : Shape) (pattern : Pattern Empty D) : Bool :=
  CommonCaseBaseCoverage.check shape [(⟨pattern, none, ()⟩ : CaseEvaluation.Arm Empty D Empty Unit)]

theorem payloadCheck_exact (shape : Shape) (pattern : Pattern Empty D) : payloadCheck shape pattern = true ↔ PayloadTotal shape pattern := by
  simpa [payloadCheck, PayloadTotal, CommonCaseBaseCoverage.Covered] using
    CommonCaseBaseCoverage.check_exact shape [(⟨pattern, none, ()⟩ : CaseEvaluation.Arm Empty D Empty Unit)]

def KnownPayload (specification : Specification) (name : Nat) (pattern : Pattern Empty D) : Prop :=
  ∃ shape, (name, shape) ∈ specification ∧ PayloadTotal shape pattern

def knownCheck (specification : Specification) (name : Nat) (pattern : Pattern Empty D) : Bool :=
  specification.any fun entry => decide (entry.1 = name) && payloadCheck entry.2 pattern

theorem knownCheck_exact (specification : Specification) (name : Nat) (pattern : Pattern Empty D) :
    knownCheck specification name pattern = true ↔ KnownPayload specification name pattern := by
  simp only [knownCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, payloadCheck_exact, KnownPayload]
  constructor
  · rintro ⟨⟨key, shape⟩, member, rfl, total⟩
    exact ⟨shape, member, total⟩
  · rintro ⟨shape, member, total⟩
    exact ⟨(name, shape), member, rfl, total⟩

inductive Total (specification : Specification) {D : Type} : Pattern Empty D → Prop where
  | wildcard : Total specification .wildcard
  | bind : Total specification (.bind name)
  | recordEnd : Total specification .recordEnd
  | field : KnownPayload specification name p → Total specification rest → Total specification (.field name p rest)
  | defaultAny : EveryValue p → Total specification rest → Total specification (.defaultField name code p rest)
  | defaultKnown : KnownPayload specification name p → Total specification rest → Total specification (.defaultField name code p rest)
  | orLeft : Total specification p → Total specification (.or p q)
  | orRight : Total specification q → Total specification (.or p q)
  | as : Total specification p → Total specification (.as p name)

def check (specification : Specification) : Pattern Empty D → Bool
  | .wildcard | .bind _ | .recordEnd => true
  | .field name p rest => knownCheck specification name p && check specification rest
  | .defaultField name _ p rest => (everyCheck p || knownCheck specification name p) && check specification rest
  | .or p q => check specification p || check specification q
  | .as p _ => check specification p
  | _ => false

theorem check_exact (specification : Specification) (pattern : Pattern Empty D) :
    check specification pattern = true ↔ Total specification pattern := by
  induction pattern with
  | wildcard => exact ⟨fun _ => .wildcard, fun _ => rfl⟩
  | bind name => exact ⟨fun _ => .bind, fun _ => rfl⟩
  | recordEnd => exact ⟨fun _ => .recordEnd, fun _ => rfl⟩
  | field name p rest ihp ihr =>
      simp only [check, Bool.and_eq_true, knownCheck_exact, ihr]
      constructor
      · rintro ⟨child, rest⟩; exact .field child rest
      · intro total; cases total with | field child rest => exact ⟨child, rest⟩
  | defaultField name code p rest ihp ihr =>
      simp only [check, Bool.and_eq_true, Bool.or_eq_true, CommonPatternNoMiss.everyCheck_exact, knownCheck_exact, ihr]
      constructor
      · rintro ⟨(child | child), rest⟩
        · exact .defaultAny child rest
        · exact .defaultKnown child rest
      · intro total
        cases total with
        | defaultAny child rest => exact ⟨Or.inl child, rest⟩
        | defaultKnown child rest => exact ⟨Or.inr child, rest⟩
  | or p q ihp ihq =>
      simp only [check, Bool.or_eq_true, ihp, ihq]
      constructor
      · rintro (left | right)
        · exact .orLeft left
        · exact .orRight right
      · intro total
        cases total with
        | orLeft left => exact Or.inl left
        | orRight right => exact Or.inr right
  | as p name ih =>
      simp only [check, ih]
      exact ⟨Total.as, fun total => by cases total; assumption⟩
  | _ => exact ⟨(fun impossible => by cases impossible), (fun total => by cases total)⟩

theorem PayloadTotal.matches (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (total : PayloadTotal shape pattern) (value : Value Empty) (valid : InShape shape value) :
    ∃ returned, (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some returned) :=
  (CommonCaseBaseMatching.matches_supported_exact floatCheck defaultEval environment pattern value valid.supported).mpr (total value valid)

/-- All actual callbacks, including errors on a missing-field default.
The cumulative environment follows the original matcher; no callback-success,
row, source typing or termination premise is required for this no-miss bound. -/
theorem Total.run_noMiss (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty))
    (total : Total specification pattern) (fields : Bindings Empty) (valid : Domain specification fields)
    (environment : Bindings Empty) :
    NoMiss (ScopedCasePatterns.run floatCheck defaultEval environment pattern (.record fields)).result := by
  induction total generalizing environment with
  | wildcard | bind | recordEnd => trivial
  | field known rest ih =>
      obtain ⟨shape, member, covered⟩ := known
      obtain ⟨item, found, itemValid⟩ := valid _ member
      obtain ⟨returned, matched⟩ := covered.matches floatCheck defaultEval environment item itemValid
      simp only [ScopedCasePatterns.run, found]
      apply CommonPatternNoMiss.andThen_noMiss
      · rw [matched]; trivial
      · intro prior; exact ih (prior ++ environment)
  | @defaultAny p rest name code child restTyped ih =>
      have children (item : Value Empty) : NoMiss
          (ScopedCasePatterns.andThen (ScopedCasePatterns.run floatCheck defaultEval environment p item)
            (fun prior => ScopedCasePatterns.run floatCheck defaultEval (prior ++ environment) rest (.record fields))).result :=
        CommonPatternNoMiss.andThen_noMiss _ _ (child.run_noMiss floatCheck defaultEval environment item)
          (fun prior => ih (prior ++ environment))
      cases found : lookup name fields with
      | some item =>
          rw [ScopedCasePatterns.default_present _ _ _ _ _ _ _ _ _ found]
          exact children item
      | none =>
          rw [ScopedCasePatterns.default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result]
          cases evaluated : (defaultEval environment code).result with
          | error => trivial
          | ok item => exact children item
  | @defaultKnown name p rest code known restTyped ih =>
      obtain ⟨shape, member, covered⟩ := known
      obtain ⟨item, found, itemValid⟩ := valid _ member
      obtain ⟨returned, matched⟩ := covered.matches floatCheck defaultEval environment item itemValid
      rw [ScopedCasePatterns.default_present _ _ _ _ _ _ _ _ _ found]
      apply CommonPatternNoMiss.andThen_noMiss
      · rw [matched]; trivial
      · intro prior; exact ih (prior ++ environment)
  | orLeft left ih =>
      have first := ih environment
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ (.record fields)).result with
      | error => trivial
      | ok option =>
          cases option with
          | none => rw [observed] at first; exact first.elim
          | some => trivial
  | orRight right ih =>
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ (.record fields)).result with
      | error => trivial
      | ok option => cases option <;> first | exact ih environment | trivial
  | as child ih =>
      have first := ih environment
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ (.record fields)).result with
      | error => trivial
      | ok option =>
          cases option with
          | none => rw [observed] at first; exact first.elim
          | some => trivial

theorem missing_default_binder_certified (code : D) :
    check [] (.defaultField 0 code (.bind 0) .recordEnd) = true := rfl

theorem refutable_missing_default_not_certified (code : D) :
    check [] (.defaultField 0 code (.literal (.int 0)) .recordEnd) = false := rfl

end Yulang.CommonRecordNoMiss
