import Yulang.CoreInference
import Yulang.PresenceDataInference

/-! Independent presence-aware data rules. This model has semantic data
predicates as types, not the required-field model's computation types/rows. -/
namespace Yulang.Core.Presence
open PresenceDataTypes
abbrev Term := Required.Term
abbrev embed := Required.embed
abbrev decode := Required.decode

inductive Typing : List Ty → Term → Ty → Prop where
  | var : context[index]? = some type → Typing context (.var index) type
  | lit (name : Inference.Base) : Typing context (.lit name) (base name)
  | emptyRecord : Typing context .emptyRecord exactEmpty
  | letE : Typing context value valueType → Typing (valueType :: context) body resultType →
      Typing context (.letE none value body) resultType
  | pair : Typing context left leftType → Typing context right rightType →
      Typing context (.pair left right) (pair leftType rightType)
  | fst : Typing context expression (pair left right) → Typing context (.fst expression) left
  | snd : Typing context expression (pair left right) → Typing context (.snd expression) right
  | record : Typing context head headType → Typing context tail tailType → Le tailType records →
      Typing context (.record label head tail) (record label headType tailType)
  | recordDefault : Typing context source sourceType → Typing context fallback fallbackType →
      Le sourceType records →
      Typing context (.recordDefault label source fallback)
        (recordDefault label sourceType fallbackType)
  | field : Typing context expression (required label payload) →
      Typing context (.field label expression) payload
  | variant : Typing context expression payload →
      Typing context (.variant label expression) (variant label payload)
  | subsume : Typing context expression source → Le source target →
      Typing context expression target

def model : TypingModel Signature.empty := ⟨List Ty, Ty, Typing⟩

theorem preserved (h : PresenceDataInference.Typing Γ e c) : Typing Γ (embed e) c := by
  induction h
  all_goals simp only [embed, Required.embed] at *
  all_goals first
    | apply Typing.var <;> assumption
    | apply Typing.lit <;> assumption
    | apply Typing.emptyRecord <;> assumption
    | apply Typing.letE <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.record <;> assumption
    | apply Typing.recordDefault <;> assumption
    | apply Typing.field <;> assumption
    | apply Typing.variant <;> assumption
    | apply Typing.subsume <;> assumption

theorem reflected (h : Typing Γ e c) : PresenceDataInference.Typing Γ (decode e) c := by
  induction h
  all_goals simp only [decode, Required.decode] at *
  all_goals first
    | apply PresenceDataInference.Typing.var <;> assumption
    | apply PresenceDataInference.Typing.lit <;> assumption
    | apply PresenceDataInference.Typing.emptyRecord <;> assumption
    | apply PresenceDataInference.Typing.letE <;> assumption
    | apply PresenceDataInference.Typing.pair <;> assumption
    | apply PresenceDataInference.Typing.fst <;> assumption
    | apply PresenceDataInference.Typing.snd <;> assumption
    | apply PresenceDataInference.Typing.record <;> assumption
    | apply PresenceDataInference.Typing.recordDefault <;> assumption
    | apply PresenceDataInference.Typing.field <;> assumption
    | apply PresenceDataInference.Typing.variant <;> assumption
    | apply PresenceDataInference.Typing.subsume <;> assumption

theorem conservative (Γ : List Ty) (e : Inference.Expr) (c : Ty) :
    PresenceDataInference.Typing Γ e c ↔ Core.Typing model Γ (embed e) c := by
  constructor
  · exact preserved
  · intro h; simpa using reflected h

end Yulang.Core.Presence
