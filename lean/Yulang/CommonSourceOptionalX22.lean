import Yulang.CommonSourceArmsSolved
import Yulang.CommonOptionalFieldBoundary
import Yulang.ScopedCaseDataProgram

/-!
# X22 through source generation, finite solved families, and actual execution

Source: spec/03b-patterns.md §3b.3:
  my read_port(config: {port?: int}): int = case config:
      {port: p} -> p
      _ -> 80

The label `port` and resolved name `p` both use 0 in their separate namespaces.
The subject is the existing optionalSource, not a strengthened required type.
PROVED here means the new source structural arm-list entry and the unchanged
actual case evaluator below, not Core.infer or completion of all of B2.
-/

namespace Yulang.CommonSourceOptionalX22

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp Formula)
open CommonSourceArmsSolved (SourceArm)
open CommonPatternSourceElaboration (DefaultTyped)

def subject : Common.Ty := CommonOptionalFieldBoundary.subject
def pattern : CasePatterns.Pattern Empty (CaseDataTerms.Expr Empty) :=
  .field 0 (.bind 0) .recordEnd
def fallback : CaseDataTerms.Expr Empty := .value (.literal (.int 80))
def firstArm : SourceArm := ⟨pattern, none, .var 0⟩
def lastArm : SourceArm := ⟨.wildcard, none, fallback⟩
def arms : List SourceArm := [firstArm, lastArm]

theorem pattern_typed :
    CommonSourcePatternTyping.Typing (DefaultTyped [] []) [] pattern subject [(0, .base .int)] := by
  constructor
  · exact (PatternBindingChecks.check_exact _).mp rfl
  · exact .field CommonOptionalFieldBoundary.optional_payload .bind
      (.narrow CommonOptionalFieldBoundary.width .recordEnd)

/-- X22 is accepted by the source traversal, including lowering, name checks,
shared allocation and optional constraints, rather than the old local rule. -/
theorem x22_source_generated :
    (CommonSourcePatternElaboration.generateSourcePattern [] ([] : PresenceGeneration.SchemeEnv (Fin 1)) []
      pattern (.var 0)).Holds Common.model (fun _ => Comp.pure Common.model subject) :=
  (CommonSourcePatternElaboration.generateSourcePattern_exact pattern [] _ [] [] []
    (CommonSyntax.EnvRel.nil Common.model) (PresenceGeneration.EnvRel.nil Common.model _) [] (.var 0)).mpr
      ⟨_, pattern_typed⟩

theorem first_arm_typed :
    CommonSourceArmGeneration.EnvironmentTyping [] [] firstArm.pattern firstArm.guard firstArm.body
      subject Common.rowEmpty (Comp.pure Common.model (.base .int)) := by
  refine .arm pattern_typed (Common.rowLe_refl _) ?_
  exact .var rfl (.mono ⟨Common.subtype_refl _, Common.rowLe_refl _⟩)

theorem last_arm_typed :
    CommonSourceArmGeneration.EnvironmentTyping [] [] lastArm.pattern lastArm.guard lastArm.body
      subject Common.rowEmpty (Comp.pure Common.model (.base .int)) := by
  refine .arm ⟨(PatternBindingChecks.check_exact _).mp rfl, .wildcard⟩ (Common.rowLe_refl _) ?_
  exact .data (.literal ⟨Common.subtype_refl _, Common.rowLe_refl _⟩)

def assignment : Fin 3 → Comp Common.model
  | ⟨0, _⟩ => Comp.pure Common.model subject
  | ⟨1, _⟩ => Comp.pure Common.model (.base .unit)
  | _ => Comp.pure Common.model (.base .int)

theorem arms_typed : ∀ arm ∈ arms,
    CommonSourceArmGeneration.EnvironmentTyping [] [] arm.pattern arm.guard arm.body
      (assignment 0).1 (assignment 1).2 (assignment 2) := by
  intro arm member
  rcases List.mem_cons.mp member with rfl | member
  · exact first_arm_typed
  · have same := List.mem_singleton.mp member
    subst arm
    exact last_arm_typed

/-- The same optional input assignment satisfies both arms, including the
first body reading p and the second body returning 80, in one generated case
environment formula. No success assumption on the first pattern is used. -/
theorem x22_case_generated :
    (CommonSourceArmsSolved.principal [] arms).Holds Common.model assignment :=
  (CommonSourceArmsSolved.principal_exact [] arms assignment).mpr arms_typed

theorem x22_real_scheme_instance :
    ∃ scheme ∈ CommonSourceArmsSolved.infer [] arms, ∃ parameters : scheme.Parameters,
      CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (CommonSourceArmsSolved.environments_instances_exact [] arms assignment).mp arms_typed

/-- Missing fields miss in the unchanged scope-aware matcher. -/
theorem x22_missing_field_misses :
    ScopedCasePatterns.run Empty.elim CaseDataTerms.defaultEval [] pattern (.record []) =
      EvaluationTrace.Logged.ofResult (.ok none) := rfl

def absentProgram : CaseDataProgram.Program Empty := ⟨.emptyRecord, arms⟩
def presentProgram (port : Int) : CaseDataProgram.Program Empty :=
  ⟨.record 0 (.value (.literal (.int port))) .emptyRecord, arms⟩

/-- Actual source evaluation reaches the second arm, with no custom callback
or assumed adequacy. The trace records arm 0 miss, arm 1, then body 1. -/
theorem x22_absent_case_result :
    ScopedCaseDataProgram.eval Empty.elim [] absentProgram =
      ⟨[.scrutinee, .source .emptyRecord, .arm 0, .arm 1, .body 1, .source fallback],
        .ok (some (.literal (.int 80)))⟩ := rfl

/-- For every integer port, the first arm returns that very integer. -/
theorem x22_present_case_result (port : Int) :
    (ScopedCaseDataProgram.eval Empty.elim [] (presentProgram port)).result =
      .ok (some (.literal (.int port))) := rfl

/-- Absence means lookup failure, not merely the special empty-record value.
For every field list and outer environment, the original matcher misses. -/
theorem x22_any_absent_field_misses (fields environment : CaseValues.Bindings Empty)
    (missing : CaseValues.lookup 0 fields = none) :
    ScopedCasePatterns.run Empty.elim CaseDataTerms.defaultEval environment pattern (.record fields) =
      EvaluationTrace.Logged.ofResult (.ok none) := by
  simp [pattern, ScopedCasePatterns.run, missing, CasePatterns.miss]

/-- A nested optional field uses the same recursive source generator rather
than falling back to the old required-field child generator. -/
def nestedPattern : CasePatterns.Pattern Empty (CaseDataTerms.Expr Empty) :=
  .field 1 pattern .recordEnd

theorem nested_pattern_typed :
    CommonSourcePatternTyping.Typing (DefaultTyped [] []) [] nestedPattern
      (Common.required 1 subject) [(0, .base .int)] := by
  constructor
  · exact (PatternBindingChecks.check_exact _).mp rfl
  · apply CommonSourcePatternTyping.RawTyping.field
      (CommonSourcePatternTyping.required_optional (Common.subtype_refl _)) pattern_typed.2
    exact .narrow ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl) .recordEnd

theorem nested_source_generated :
    (CommonSourcePatternElaboration.generateSourcePattern [] ([] : PresenceGeneration.SchemeEnv (Fin 1)) []
      nestedPattern (.var 0)).Holds Common.model (fun _ => Comp.pure Common.model (Common.required 1 subject)) :=
  (CommonSourcePatternElaboration.generateSourcePattern_exact nestedPattern [] _ [] [] []
    (CommonSyntax.EnvRel.nil Common.model) (PresenceGeneration.EnvRel.nil Common.model _) [] (.var 0)).mpr
      ⟨_, nested_pattern_typed⟩

/-- One certificate contains the generated case constraints and both runtime
branches. It does not alter the historical strict_rejects theorem. -/
theorem x22_proved :
    (CommonSourceArmsSolved.principal [] arms).Holds Common.model assignment ∧
    (ScopedCaseDataProgram.eval Empty.elim [] absentProgram).result = .ok (some (.literal (.int 80))) ∧
    (∀ port : Int, (ScopedCaseDataProgram.eval Empty.elim [] (presentProgram port)).result =
      .ok (some (.literal (.int port)))) :=
  ⟨x22_case_generated, congrArg EvaluationTrace.Logged.result x22_absent_case_result, x22_present_case_result⟩

end Yulang.CommonSourceOptionalX22
