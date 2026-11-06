import Yulang.CaseDataTerms
import Yulang.CaseCoverageSafety

/-!
# Finite recursively nested case expressions

Case scrutinees and arm bodies are recursive expressions, not external
semantic callbacks. Products and computed lets can contain cases too. Default
and guard expressions remain the concrete `CaseDataTerms` leaves. Their scope
is the explicitly supplied resolved lexical environment; no source default
scope policy is added here.

The independent syntax typing requires declarative structural coverage and
syntax typings only for default codes actually present in the arm patterns.
The mutual safety theorem derives successful evaluation of every nested case
from those syntax derivations. It never assumes successful evaluation of an
arbitrary expression or supplies a body-soundness oracle.

A raw expression can still contain an uncovered case. Its evaluator returns
`none`, while the theorem proves this cannot happen in a typed expression.
Recursion here is finite syntax nesting, not recursive source functions.
-/

namespace Yulang.CaseTree

open CaseValues LiteralValues EvaluationTrace

abbrev Data (F : Type) := CaseDataTerms.Expr F
abbrev Pat (F : Type) := CasePatterns.Pattern F (Data F)

mutual
  inductive Expr (F : Type) where
    | leaf : Data F → Expr F
    | caseE : Expr F → Arms F → Expr F
    | pair : Expr F → Expr F → Expr F
    | letE : Nat → Expr F → Expr F → Expr F

  inductive Arms (F : Type) where
    | nil
    | cons : Pat F → Option (Data F) → Expr F → Arms F → Arms F
end

abbrev Result (F : Type) :=
  Logged (CaseEvaluation.Event (Data F)) CaseDataTerms.Error (Option (Value F))

def pure (value : Value F) : Result F := Logged.ofResult (.ok (some value))
def noMatch : Result F := Logged.ofResult (.ok none)

def metadata (pattern : Pat F) (guard : Option (Data F)) :
    CaseEvaluation.Arm F (Data F) (Data F) Unit := ⟨pattern, guard, ()⟩

def Arms.coverage : Arms F → List (CaseCoverage.Arm F (Data F))
  | .nil => []
  | .cons pattern guard _ rest => ⟨pattern, guard.isSome⟩ :: rest.coverage

mutual
  def eval (floatCheck : F → F → Bool) (environment : Bindings F) : Expr F → Result F
    | .leaf code => (CaseDataTerms.eval environment code).bind pure
    | .caseE scrutinee arms => Logged.prepend [.scrutinee] <|
        (eval floatCheck environment scrutinee).bind fun selected => match selected with
          | none => noMatch
          | some value => evalArms floatCheck environment value 0 arms
    | .pair first last => (eval floatCheck environment first).bind fun selected => match selected with
        | none => noMatch
        | some left => (eval floatCheck environment last).bind fun selected => match selected with
          | none => noMatch
          | some right => pure (.pair left right)
    | .letE name definition body => (eval floatCheck environment definition).bind fun selected =>
        match selected with
        | none => noMatch
        | some value => eval floatCheck ((name, value) :: environment) body

  def evalArms (floatCheck : F → F → Bool) (environment : Bindings F)
      (value : Value F) (index : Nat) : Arms F → Result F
    | .nil => noMatch
    | .cons pattern guard body rest => Logged.prepend [.arm index] <|
        (CaseEvaluation.testArm floatCheck (CaseDataTerms.defaultEval environment)
          (CaseDataTerms.guardEval environment) index (metadata pattern guard) value).bind fun selected =>
          match selected with
          | none => evalArms floatCheck environment value (index + 1) rest
          | some bindings => Logged.prepend [.body index] <|
              eval floatCheck (bindings ++ environment) body
end

mutual
  /-- No evaluator or successful execution appears in this judgement. -/
  inductive Typing : List (Nat × Ty F) → Expr F → Ty F → Prop where
    | leaf : CaseDataTerms.Typing types code target → Typing types (.leaf code) target
    | caseE {domain : CaseCoverage.Domain} {defaultDomains : Data F → CaseCoverage.Domain} :
        Typing types scrutinee (domain.denote F) → ArmsTyping types arms (domain.denote F) target →
        CaseCoverage.Covered defaultDomains arms.coverage domain →
        (∀ code ∈ CaseCoverage.armDefaults arms.coverage,
          CaseDataTerms.Typing types code ((defaultDomains code).denote F)) →
        Typing types (.caseE scrutinee arms) target
    | caseVariants {row : CaseCoverage.VariantRow} {defaultDomains : Data F → CaseCoverage.Domain} :
        Typing types scrutinee (Ty.variants (CaseCoverage.semanticRow row)) →
        ArmsTyping types arms (Ty.variants (CaseCoverage.semanticRow row)) target →
        CaseCoverage.VariantsCovered defaultDomains arms.coverage row →
        (∀ code ∈ CaseCoverage.armDefaults arms.coverage,
          CaseDataTerms.Typing types code ((defaultDomains code).denote F)) →
        Typing types (.caseE scrutinee arms) target
    | pair : Typing types first left → Typing types last right →
        Typing types (.pair first last) (Ty.pair left right)
    | letE : Typing types definition input → Typing ((name, input) :: types) body output →
        Typing types (.letE name definition body) output
    | widen : Typing types expression input → Ty.Le input output → Typing types expression output

  inductive ArmsTyping : List (Nat × Ty F) → Arms F → Ty F → Ty F → Prop where
    | nil : ArmsTyping types .nil input target
    | cons {guard : Option (Data F)} : CasePatterns.Typing (CaseDataTerms.DefaultTyped types) pattern input bindings →
        (∀ code, guard = some code → CaseDataTerms.GuardTyped types code bindings) →
        Typing (bindings ++ types) body target → ArmsTyping types rest input target →
        ArmsTyping types (.cons pattern guard body rest) input target
end

/-- Only an unguarded, actually matching pattern can witness structural
coverage for a particular value. This is discharged by `covered_matches`. -/
def Matching (floatCheck : F → F → Bool) (environment : Bindings F)
    (arms : Arms F) (value : Value F) : Prop :=
  ∃ arm ∈ arms.coverage, arm.guarded = false ∧ ∃ bindings,
    (CasePatterns.run floatCheck (CaseDataTerms.defaultEval environment) arm.pattern value).result =
      .ok (some bindings)

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl


/-- Typed finite nesting evaluates to a value of the declared type, using
only validity of the external environment as a semantic premise. The mutual
syntax induction also proves that a typed list with a matching unguarded arm
executes one of its bodies. -/
theorem typing_evaluates {F : Type} (floatCheck : F → F → Bool)
    {types : List (Nat × Ty F)} {expression : Expr F} {target : Ty F}
    (typed : Typing types expression target) :
    ∀ (environment : Bindings F), BindingsHold types environment →
      ∃ value, (eval floatCheck environment expression).result = .ok (some value) ∧ target value := by
  induction typed using Typing.rec
      (motive_2 := fun types arms input target _ =>
        ∀ (environment : Bindings F), BindingsHold types environment →
          ∀ (value : Value F), input value → Matching floatCheck environment arms value →
            ∀ (index : Nat), ∃ result,
              (evalArms floatCheck environment value index arms).result = .ok (some result) ∧
                target result) with
  | leaf leafTyped =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := CaseDataTerms.typing_evaluates leafTyped environment valid
      exact ⟨value, by simp [eval, Logged.bind_result, evaluated, pure, Logged.ofResult], valueValid⟩
  | @caseE types scrutinee arms target domain defaultDomains scrutineeTyped armsTyped covered defaults
      scrutineeIH armsIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := scrutineeIH environment valid
      have defaultSound : CaseCoverage.DefaultsSoundFor defaultDomains
          (CaseDataTerms.defaultEval environment) (CaseCoverage.armDefaults arms.coverage) := by
        intro code used
        exact CaseDataTerms.typing_evaluates (defaults code used) environment valid
      have matched : Matching floatCheck environment arms value :=
        CaseCoverage.covered_matches floatCheck (CaseDataTerms.defaultEval environment)
          defaultDomains arms.coverage domain covered value valueValid defaultSound
      obtain ⟨result, ran, resultValid⟩ := armsIH environment valid value valueValid matched 0
      exact ⟨result, by simp [eval, Logged.bind_result, evaluated, ran], resultValid⟩
  | @caseVariants types scrutinee arms target row defaultDomains scrutineeTyped armsTyped covered defaults
      scrutineeIH armsIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := scrutineeIH environment valid
      have defaultSound : CaseCoverage.DefaultsSoundFor defaultDomains
          (CaseDataTerms.defaultEval environment) (CaseCoverage.armDefaults arms.coverage) := by
        intro code used
        exact CaseDataTerms.typing_evaluates (defaults code used) environment valid
      have matched : Matching floatCheck environment arms value :=
        CaseCoverage.variants_covered_matches floatCheck (CaseDataTerms.defaultEval environment)
          defaultDomains arms.coverage row covered value
          ((CaseCoverage.variantHolds_semanticRow row value).mpr valueValid) defaultSound
      obtain ⟨result, ran, resultValid⟩ := armsIH environment valid value valueValid matched 0
      exact ⟨result, by simp [eval, Logged.bind_result, evaluated, ran], resultValid⟩
  | pair firstTyped lastTyped firstIH lastIH =>
      intro environment valid
      obtain ⟨first, firstEval, firstValid⟩ := firstIH environment valid
      obtain ⟨last, lastEval, lastValid⟩ := lastIH environment valid
      exact ⟨.pair first last, by simp [eval, Logged.bind_result, firstEval, lastEval, pure,
        Logged.ofResult], firstValid, lastValid⟩
  | letE definitionTyped bodyTyped definitionIH bodyIH =>
      intro environment valid
      obtain ⟨first, firstEval, firstValid⟩ := definitionIH environment valid
      obtain ⟨last, lastEval, lastValid⟩ := bodyIH _ (.cons firstValid valid)
      exact ⟨last, by simp [eval, Logged.bind_result, firstEval, lastEval], lastValid⟩
  | widen inner below innerIH =>
      intro environment valid
      obtain ⟨value, evaluated, valueValid⟩ := innerIH environment valid
      exact ⟨value, evaluated, below value valueValid⟩
  | nil =>
      rename_i environment valid value valueValid matched index
      obtain ⟨arm, impossible, _⟩ := matched
      cases impossible
  | @cons types pattern input bindings body target rest guard patternTyped guardTyped bodyTyped restTyped
      bodyIH restIH =>
      rename_i environment valid value valueValid matched index
      have safe := CaseEvaluation.testArm_typed floatCheck (CaseDataTerms.defaultEval environment)
        (CaseDataTerms.guardEval environment) (CaseDataTerms.default_sound environment types valid)
        (CaseDataTerms.guard_sound environment types valid) (arm := metadata pattern guard)
        patternTyped guardTyped value valueValid index
      simp only [evalArms, Logged.prepend_result, Logged.bind_result]
      cases observed : (CaseEvaluation.testArm floatCheck (CaseDataTerms.defaultEval environment)
          (CaseDataTerms.guardEval environment) index (metadata pattern guard) value).result with
      | error error => rw [observed] at safe; cases safe
      | ok option =>
          rw [observed] at safe
          cases option with
          | some actual =>
              obtain ⟨result, evaluated, resultValid⟩ := bodyIH
                (actual ++ environment) (safe.append valid)
              exact ⟨result, by simp [evaluated], resultValid⟩
          | none =>
              have restMatching : Matching floatCheck environment rest value := by
                obtain ⟨coveredArm, member, unguarded, actual, successful⟩ := matched
                rcases List.mem_cons.mp member with same | member
                · subst coveredArm
                  cases guard with
                  | some code => cases unguarded
                  | none =>
                      simp [CaseEvaluation.testArm, metadata, Logged.bind_result, successful,
                        CasePatterns.success, Logged.ofResult] at observed
                · exact ⟨coveredArm, member, unguarded, actual, successful⟩
              obtain ⟨result, evaluated, resultValid⟩ := restIH environment valid value valueValid
                restMatching (index + 1)
              exact ⟨result, by simp [evaluated], resultValid⟩

/-- Executable coverage acceptance constructs the independent case rule.
Nested scrutinees and bodies are checked through their own syntax derivations. -/
theorem case_typing_of_checked (types : List (Nat × Ty F))
    (scrutinee : Expr F) (arms : Arms F) (input : CaseCoverage.Domain) (target : Ty F)
    (defaultDomains : Data F → CaseCoverage.Domain)
    (scrutineeTyped : Typing types scrutinee (input.denote F))
    (armsTyped : ArmsTyping types arms (input.denote F) target)
    (defaults : ∀ code ∈ CaseCoverage.armDefaults arms.coverage,
      CaseDataTerms.Typing types code ((defaultDomains code).denote F))
    (checked : CaseCoverage.check defaultDomains arms.coverage input = true) :
    Typing types (.caseE scrutinee arms) target :=
  .caseE scrutineeTyped armsTyped ((CaseCoverage.check_exact _ _ _).mp checked) defaults

theorem checked_case_evaluates (floatCheck : F → F → Bool)
    (types : List (Nat × Ty F)) (environment : Bindings F) (valid : BindingsHold types environment)
    (scrutinee : Expr F) (arms : Arms F) (input : CaseCoverage.Domain) (target : Ty F)
    (defaultDomains : Data F → CaseCoverage.Domain)
    (scrutineeTyped : Typing types scrutinee (input.denote F))
    (armsTyped : ArmsTyping types arms (input.denote F) target)
    (defaults : ∀ code ∈ CaseCoverage.armDefaults arms.coverage,
      CaseDataTerms.Typing types code ((defaultDomains code).denote F))
    (checked : CaseCoverage.check defaultDomains arms.coverage input = true) :
    ∃ value, (eval floatCheck environment (.caseE scrutinee arms)).result = .ok (some value) ∧
      target value :=
  typing_evaluates floatCheck
    (case_typing_of_checked types scrutinee arms input target defaultDomains
      scrutineeTyped armsTyped defaults checked) environment valid

/-- The closed-row rule preserves entire merged payloads and uses the
same executable tag coverage check as the one-node concrete program. -/
theorem checked_variants_evaluate (floatCheck : F → F → Bool)
    (types : List (Nat × Ty F)) (environment : Bindings F) (valid : BindingsHold types environment)
    (scrutinee : Expr F) (arms : Arms F) (row : CaseCoverage.VariantRow) (target : Ty F)
    (defaultDomains : Data F → CaseCoverage.Domain)
    (scrutineeTyped : Typing types scrutinee (Ty.variants (CaseCoverage.semanticRow row)))
    (armsTyped : ArmsTyping types arms (Ty.variants (CaseCoverage.semanticRow row)) target)
    (defaults : ∀ code ∈ CaseCoverage.armDefaults arms.coverage,
      CaseDataTerms.Typing types code ((defaultDomains code).denote F))
    (checked : CaseCoverage.checkVariants defaultDomains arms.coverage row = true) :
    ∃ value, (eval floatCheck environment (.caseE scrutinee arms)).result = .ok (some value) ∧
      target value :=
  typing_evaluates floatCheck (.caseVariants scrutineeTyped armsTyped
    ((CaseCoverage.checkVariants_exact _ _ _).mp checked) defaults) environment valid

theorem closed_typing_evaluates (floatCheck : F → F → Bool)
    (expression : Expr F) (target : Ty F) (typed : Typing [] expression target) :
    ∃ value, (eval floatCheck [] expression).result = .ok (some value) ∧ target value :=
  typing_evaluates floatCheck typed [] .nil

theorem typed_no_unmatched (floatCheck : F → F → Bool)
    (types : List (Nat × Ty F)) (environment : Bindings F) (valid : BindingsHold types environment)
    (expression : Expr F) (target : Ty F) (typed : Typing types expression target) :
    (eval floatCheck environment expression).result ≠ .ok none := by
  obtain ⟨value, evaluated, _⟩ := typing_evaluates floatCheck typed environment valid
  simp [evaluated]

end Yulang.CaseTree
