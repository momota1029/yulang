import Yulang.CommonOptionalFieldSafety
import Yulang.CommonPatternFormulaEquivalence

/-! Exact separation of the two local field rules at the open design question.
The optional rule has a real finite model/solver instance and may miss an
empty record. The historical required rule cannot type that input. This is
not an E2 counterexample to full B2, whose rule choice remains unapproved. -/

namespace Yulang.CommonOptionalFieldBoundary

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment (NamedTypes)
open CasePatterns (Pattern)
open EvaluationTrace (Logged)

def subject : Common.Ty := CommonDefaultRequired.optionalSource 0 (.base .int)
def pattern : Pattern Empty D := .field 0 (.bind 0) .recordEnd

theorem optional_payload : CommonDefaultRequired.OptionalPayload 0 subject (.base .int) :=
  (CommonDefaultRequired.optionalPayload_optionalSource 0 _ _).mpr (Common.subtype_refl _)

theorem width : Common.Subtype subject Common.emptyRecord :=
  (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr
    (CommonOptionalBound.optional_payload_shape _ _ _ optional_payload)

theorem permissive_typed (defaults : NamedTypes → D → Common.Ty → Prop) (types : NamedTypes) :
    CommonOptionalField.Typing defaults types 0 (.bind 0) .recordEnd subject [(0, .base .int)] :=
  .field (Common.subtype_refl _) optional_payload .bind (.narrow width .recordEnd)

theorem strict_rejects (defaults : NamedTypes → D → Common.Ty → Prop) (types bindings : NamedTypes) :
    ¬ CommonAlignedPatternTyping.RawTyping defaults types pattern subject bindings := by
  intro typed
  obtain ⟨original, payload, left, right, output, below, required, first, last⟩ :=
    CommonAlignedPatternInversion.field_iff.mp typed
  have emptyTyped : Core.CommonData.ValueTyping Common.model (.record []) (Comp.pure Common.model subject) :=
    .emptyRecord ⟨CommonBoundCoalescing.le_union_left _ _, Common.rowLe_refl _⟩
  obtain ⟨item, impossible, safe⟩ := CommonPatternLookup.required_lookup [] _ 0 payload emptyTyped (Common.subtype_trans below required)
  cases impossible

theorem actual_empty_miss (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged E R (CaseValues.Value Empty)) (environment : CaseValues.Bindings Empty) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern (.record []) = Logged.ofResult (.ok none) := rfl

def principal : Formula (Fin 2) :=
  CommonOptionalField.generate 0 (.bind 0) .recordEnd [] [] (.var 0) [(0, .var 1)]

def assignment : Fin 2 → Comp Common.model
  | ⟨0, _⟩ => Comp.pure Common.model subject
  | _ => Comp.pure Common.model (.base .int)

theorem generated_model : principal.Holds Common.model assignment :=
  (CommonOptionalField.generate_exact 0 (.bind 0) .recordEnd assignment [] [] (EnvRel.nil Common.model assignment)
    [] (.var 0) [(0, .var 1)]).mpr (permissive_typed _ [])

theorem principal_safe : CommonPatternGenerationProvenance.SafeFormula principal := by
  have environmentGood : CommonPatternGenerationProvenance.SafeEnvironment ([] : SchemeEnv (Fin 2)) := by
    constructor <;> intro scheme member <;> cases member
  apply CommonOptionalField.safe_generate 0 (.bind 0) .recordEnd [] environmentGood []
    (by intro binding member; cases member) (.var 0) ⟨rfl, rfl, rfl⟩ [(0, .var 1)]
  intro binding member
  have same : binding = (0, .var 1) := List.mem_singleton.mp member
  subst binding
  exact ⟨rfl, rfl⟩

theorem real_scheme_instance :
    ∃ scheme ∈ CommonPatternFiniteSchemes.infer principal, ∃ parameters : scheme.Parameters,
      CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (CommonPatternFiniteSchemes.formula_instances_exact principal principal_safe assignment).mp generated_model

end Yulang.CommonOptionalFieldBoundary
