import Yulang.CaseDataProgram

/-!
# Executable coverage examples and a proved completeness boundary

The interval example deliberately records a semantically exhaustive program
that this conservative checker does not yet recognize. This is an unfinished
checker, not a new language rule rejecting the program.
-/

namespace Yulang.CaseCoverageExamples

open CaseValues CasePatterns CaseCoverage LiteralValues EvaluationTrace

def floatCheck : Empty → Empty → Bool := Empty.elim

def noDefault : Empty → Logged String String (Value Empty) := Empty.elim

def integerSplit : List (CaseCoverage.Arm Empty Empty) :=
  [⟨.intRange none (some 0), false⟩, ⟨.intRange (some 1) none, false⟩]

/-- The structural checker currently lacks interval-union coverage. -/
theorem integer_split_not_yet_recognized :
    check CaseCoverage.Examples.noDefaults integerSplit (.base .int) = false := rfl

/-- Nevertheless every arbitrary-precision integer matches one of the two
unguarded arms. Thus the rejection above is demonstrably incompleteness. -/
theorem integer_split_semantically_exhaustive (integer : Int) :
    ∃ arm ∈ integerSplit, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck noDefault arm.pattern (.literal (.int integer))).result =
        .ok (some bindings) := by
  by_cases small : integer ≤ 0
  · refine ⟨⟨.intRange none (some 0), false⟩, by simp [integerSplit], rfl, [], ?_⟩
    simp [CasePatterns.run, intRangeCheck, small, success, Logged.ofResult]
  · have large : 1 ≤ integer := by omega
    refine ⟨⟨.intRange (some 1) none, false⟩, by simp [integerSplit], rfl, [], ?_⟩
    simp [CasePatterns.run, intRangeCheck, large, success, Logged.ofResult]

def twoTags : VariantRow := Variants.Merged.normalize Domain.union [(0, .base .unit), (1, .base .bool)]

theorem missing_tag_not_covered :
    checkVariants (F := Empty) CaseCoverage.Examples.noDefaults [⟨.variant 0 .wildcard, false⟩] twoTags = false := rfl

def boolExpr (value : Bool) : CaseDataTerms.Expr Empty := .value (.literal (.bool value))
def intExpr (value : Int) : CaseDataTerms.Expr Empty := .value (.literal (.int value))

theorem boolExpr_typed (types : List (Nat × Ty Empty)) (value : Bool) :
    CaseDataTerms.Typing types (boolExpr value) (Ty.literal .bool) :=
  .widen .value (by intro item same; cases same; rfl)

theorem intExpr_typed (types : List (Nat × Ty Empty)) (value : Int) :
    CaseDataTerms.Typing types (intExpr value) (Ty.literal .int) :=
  .widen .value (by intro item same; cases same; rfl)

def guardedFirst : CaseDataProgram.Arm Empty := ⟨.wildcard, some (boolExpr false), intExpr 1⟩
def falseArm : CaseDataProgram.Arm Empty := ⟨.literal (.bool false), none, intExpr 2⟩
def trueArm : CaseDataProgram.Arm Empty := ⟨.literal (.bool true), none, intExpr 3⟩

def booleanProgram : CaseDataProgram.Program Empty := ⟨boolExpr true, [guardedFirst, falseArm, trueArm]⟩

def unusedDomains : CaseDataTerms.Expr Empty → Domain := fun _ => .any

private theorem guardedFirst_typed :
    CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped []) (CaseDataTerms.GuardTyped [])
      (CaseDataTerms.BodyTyped []) guardedFirst (Domain.denote Empty (.base .bool)) (Ty.literal .int) := by
  refine .arm .wildcard ?_ (intExpr_typed [] 1)
  intro code same
  have equal : boolExpr false = code := Option.some.inj same
  subst code
  exact boolExpr_typed [] false

private theorem falseArm_typed :
    CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped []) (CaseDataTerms.GuardTyped [])
      (CaseDataTerms.BodyTyped []) falseArm (Domain.denote Empty (.base .bool)) (Ty.literal .int) := by
  exact .arm (.literal (fun _ valid => valid)) (by intro code absent; cases absent) (intExpr_typed [] 2)

private theorem trueArm_typed :
    CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped []) (CaseDataTerms.GuardTyped [])
      (CaseDataTerms.BodyTyped []) trueArm (Domain.denote Empty (.base .bool)) (Ty.literal .int) := by
  exact .arm (.literal (fun _ valid => valid)) (by intro code absent; cases absent) (intExpr_typed [] 3)

theorem booleanProgram_typed :
    CaseDataProgram.Typing [] unusedDomains booleanProgram (Ty.literal .int) := by
  apply CaseDataProgram.Typing.uniform (.base .bool) (boolExpr_typed [] true)
  · intro code used
    simp [armDefaults, coverageArms, booleanProgram, guardedFirst, falseArm, trueArm, patternDefaults] at used
  · intro arm member
    simp only [booleanProgram, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact guardedFirst_typed
    · exact falseArm_typed
    · exact trueArm_typed
  · exact (check_exact _ _ _).mp rfl

theorem booleanProgram_evaluates_from_typing :
    ∃ result, (CaseDataProgram.eval floatCheck [] booleanProgram).result = .ok (some result) ∧
      Ty.literal .int result :=
  CaseDataProgram.closed_typing_evaluates floatCheck booleanProgram_typed

/-- Guard false skips its body, then literal arms are tried in written order. -/
theorem booleanProgram_written_order :
    CaseDataProgram.eval floatCheck [] booleanProgram =
      ⟨[.scrutinee, .source (boolExpr true), .arm 0, .guard 0, .source (boolExpr false),
        .arm 1, .arm 2, .body 2, .source (intExpr 3)], .ok (some (.literal (.int 3)))⟩ := rfl

def fallback : CaseDataTerms.Expr Empty := intExpr 41

def defaultPattern : Pattern Empty (CaseDataTerms.Expr Empty) :=
  .defaultField 0 fallback (.bind 1) .recordEnd

def defaultInput : Domain := .optional 0 (.base .int) .records

def defaultDomains : CaseDataTerms.Expr Empty → Domain := fun _ => .base .int

theorem default_pattern_covered : checkOne defaultDomains defaultPattern defaultInput = true := rfl

/-- Only the actual default expression is typed; unbound raw expressions are
not assumed to succeed merely because they inhabit the same syntax type. -/
theorem default_local_annotations :
    ∀ code ∈ patternDefaults defaultPattern,
      CaseDataTerms.Typing [] code ((defaultDomains code).denote Empty) := by
  intro code used
  simp only [defaultPattern, patternDefaults, List.nil_append, List.mem_singleton] at used
  subst code
  exact intExpr_typed [] 41

theorem an_unused_raw_code_still_fails :
    (CaseDataTerms.eval [] (.var 999 : CaseDataTerms.Expr Empty)).result =
      .error (.unboundVariable 999) := rfl

theorem default_present_has_no_fallback_visit :
    CasePatterns.run floatCheck (CaseDataTerms.defaultEval []) defaultPattern
      (.record [(0, .literal (.int 9))]) =
      ⟨[], .ok (some [(1, .literal (.int 9))])⟩ := rfl

theorem default_absent_visits_fallback :
    CasePatterns.run floatCheck (CaseDataTerms.defaultEval []) defaultPattern (.record []) =
      ⟨[.source fallback], .ok (some [(1, .literal (.int 41))])⟩ := rfl

/-- A concrete default-bearing program also uses the independent coverage
judgement and syntax typing, with no per-arm success hypothesis. -/
def defaultProgram : CaseDataProgram.Program Empty :=
  ⟨.emptyRecord, [⟨defaultPattern, none, .var 1⟩]⟩

private theorem default_scrutinee_typed :
    CaseDataTerms.Typing [] defaultProgram.scrutinee (defaultInput.denote Empty) := by
  apply CaseDataTerms.Typing.widen .emptyRecord
  intro value same
  cases same
  refine ⟨?_, True.intro⟩
  intro value missing
  cases missing

private theorem default_arm_typed :
    CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped []) (CaseDataTerms.GuardTyped [])
      (CaseDataTerms.BodyTyped []) ⟨defaultPattern, none, .var 1⟩
      (defaultInput.denote Empty) (Ty.union (Ty.literal .int) (Ty.literal .int)) := by
  apply CaseEvaluation.ArmTyping.arm
  · apply CasePatterns.Typing.defaultField
    · intro value valid; exact valid.1
    · exact intExpr_typed [] 41
    · exact .bind
    · exact .narrow (fun value valid => valid.2) .recordEnd
  · intro code missing; cases missing
  · exact CaseDataTerms.Typing.var (by rfl)

theorem defaultProgram_typed :
    CaseDataProgram.Typing [] defaultDomains defaultProgram (Ty.union (Ty.literal .int) (Ty.literal .int)) := by
  apply CaseDataProgram.Typing.uniform defaultInput default_scrutinee_typed
  · intro code used
    apply default_local_annotations code
    simpa [armDefaults, coverageArms, defaultProgram] using used
  · intro arm member
    have same : arm = ⟨defaultPattern, none, .var 1⟩ := by simpa [defaultProgram] using member
    subst arm
    exact default_arm_typed
  · exact (check_exact _ _ _).mp rfl

theorem defaultProgram_evaluates_from_typing :
    ∃ result, (CaseDataProgram.eval floatCheck [] defaultProgram).result = .ok (some result) ∧
      (Ty.union (Ty.literal .int) (Ty.literal .int)) result :=
  CaseDataProgram.closed_typing_evaluates floatCheck defaultProgram_typed


/-- A two-constructor nominal enum, with unit and integer payloads. -/
def enumDomain : Domain := .union (.nominal 9 0 (.base .unit)) (.nominal 9 1 (.base .int))

def enumPayloads : Variants.Merged.Row Nat (Ty Empty) :=
  Variants.Merged.normalize Ty.union [(0, Ty.literal .unit), (1, Ty.literal .int)]

theorem enumDomain_below_nominals : Ty.Le (enumDomain.denote Empty) (Ty.nominals 9 enumPayloads) := by
  intro value valid
  cases value with
  | nominal typeId ctorId item =>
      rcases valid with first | last
      · obtain ⟨sameType, sameCtor, payload⟩ := first
        subst typeId; subst ctorId
        exact ⟨rfl, Ty.literal .unit, rfl, payload⟩
      · obtain ⟨sameType, sameCtor, payload⟩ := last
        subst typeId; subst ctorId
        exact ⟨rfl, Ty.literal .int, rfl, payload⟩
  | _ => rcases valid with impossible | impossible <;> cases impossible

def enumEmptyArm : CaseDataProgram.Arm Empty := ⟨.nominal 9 0 .wildcard, none, intExpr 10⟩
def enumPayloadArm : CaseDataProgram.Arm Empty := ⟨.nominal 9 1 (.bind 7), none, .var 7⟩

def enumProgram : CaseDataProgram.Program Empty :=
  ⟨.value (.nominal 9 1 (.literal (.int 77))), [enumEmptyArm, enumPayloadArm]⟩

private theorem enumEmptyArm_typed :
    CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped []) (CaseDataTerms.GuardTyped [])
      (CaseDataTerms.BodyTyped []) enumEmptyArm (enumDomain.denote Empty) (Ty.literal .int) := by
  refine .arm (.narrow enumDomain_below_nominals (.mergedNominal enumPayloads rfl .wildcard)) ?_
    (intExpr_typed [] 10)
  intro code missing
  cases missing

private theorem enumPayloadArm_typed :
    CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped []) (CaseDataTerms.GuardTyped [])
      (CaseDataTerms.BodyTyped []) enumPayloadArm (enumDomain.denote Empty) (Ty.literal .int) := by
  refine .arm (.narrow enumDomain_below_nominals (.mergedNominal enumPayloads rfl .bind)) ?_ ?_
  · intro code missing; cases missing
  · exact CaseDataTerms.Typing.var rfl

theorem enumProgram_typed :
    CaseDataProgram.Typing [] unusedDomains enumProgram (Ty.literal .int) := by
  apply CaseDataProgram.Typing.uniform enumDomain
  · apply CaseDataTerms.Typing.widen .value
    intro value same
    cases same
    exact .inr ⟨rfl, rfl, rfl⟩
  · intro code used
    simp [armDefaults, coverageArms, enumProgram, enumEmptyArm, enumPayloadArm, patternDefaults] at used
  · intro arm member
    simp only [enumProgram, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact enumEmptyArm_typed
    · exact enumPayloadArm_typed
  · exact (check_exact _ _ _).mp rfl

theorem enumProgram_evaluates_from_typing :
    ∃ result, (CaseDataProgram.eval floatCheck [] enumProgram).result = .ok (some result) ∧
      Ty.literal .int result :=
  CaseDataProgram.closed_typing_evaluates floatCheck enumProgram_typed

theorem enumProgram_preserves_payload :
    (CaseDataProgram.eval floatCheck [] enumProgram).result = .ok (some (.literal (.int 77))) := rfl

end Yulang.CaseCoverageExamples
