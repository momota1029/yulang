import Yulang.CoreSourceInference
import Yulang.CorePresenceInference
import Yulang.PresenceDataSafety

/-! Real Core-entry computations. Unknown-base lambda and effectful fallback
inference remain outside these separate entries, and are not claimed here. -/
namespace Yulang.Core.InferenceExamples

abbrev Term := Required.Term
open PresenceDataTypes

def present : Term :=
  .recordDefault 0 (.record 0 (.lit .str) (.record 1 (.lit .bool) .emptyRecord)) (.lit .int)

def absent : Term :=
  .recordDefault 0 (.record 1 (.lit .bool) .emptyRecord) (.lit .int)

def hiddenInvalid : Term :=
  .recordDefault 0 (.record 0 (.lit .str) .emptyRecord) (.field 2 .emptyRecord)

def shadowed : Term :=
  .record 0 (.lit .str) (.record 0 (.lit .int) (.record 1 (.lit .bool) .emptyRecord))

theorem present_inferred : PresenceInference.infer present =
    .solved (.record (.cons 0 (.base .str) (.cons 1 (.base .bool) .nil))) := rfl

theorem absent_inferred : PresenceInference.infer absent =
    .solved (.record (.cons 1 (.base .bool) (.cons 0 (.base .int) .nil))) := rfl

theorem shadowed_inferred : PresenceInference.infer shadowed =
    .solved (.record (.cons 0 (.base .str) (.cons 1 (.base .bool) .nil))) := rfl

theorem hidden_invalid_rejected : PresenceInference.infer hiddenInvalid = .rejected := rfl

theorem hidden_invalid_untypable : ¬ ∃ target, Typing Presence.model [] hiddenInvalid target :=
  ((PresenceInference.infer_rejected_iff hiddenInvalid).mp hidden_invalid_rejected).2

theorem hidden_fallback_evaluated :
    SourceDataRuntime.eval [] (Required.decode hiddenInvalid) = .error (.missingField 2) := rfl

/-- A syntactically invalid Core input cannot fall through the legacy
decoder's default literal, even when decoding alone would produce one. -/
theorem new_syntax_unsupported :
    RequiredInference.infer (.free 0) = .unsupported ∧
      PresenceInference.infer (.free 0) = .unsupported := ⟨rfl, rfl⟩

theorem missing_field_rejected :
    (RequiredInference.infer (.field 0 .emptyRecord)).status = .rejected := by decide +kernel

theorem default_legacy_unsupported : RequiredInference.infer present = .unsupported := rfl

/-- The open operator contract is quantified over arbitrary input predicates
and every target. This is a typing theorem, not an unknown-base inference run. -/
theorem unknown_default_principal (label : Nat) (payload fallback target : Ty) :
    Typing Presence.model [optional label payload, fallback]
      (.recordDefault label (.var 0) (.var 1)) target ↔
        Le (recordDefault label (optional label payload) fallback) target := by
  exact (Presence.conservative _ (PresenceDataSafety.defaultOperator label) target).symm.trans
    (PresenceDataSafety.optional_operator_principal label payload fallback target)

theorem unknown_default_union (label : Nat) (payload fallback : Ty) :
    Typing Presence.model [optional label payload, fallback]
      (.recordDefault label (.var 0) (.var 1)) (required label (union payload fallback)) :=
  (unknown_default_principal label payload fallback _).mpr
    (recordDefault_optional label _ payload fallback (le_refl _))

end Yulang.Core.InferenceExamples
