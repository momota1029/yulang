import Yulang.CoreInferenceSyntax
import Yulang.CorePresence

/-! Executable presence-data inference on Core, with an exact syntax gate.
This entry keeps the existing predicate/Shape model. It is deliberately separate
from `RequiredInference.infer` until the common regular solver is constructed. -/
namespace Yulang.Core.PresenceInference

open PresenceDataTypes
open PresenceDataShapes (Shape)
abbrev Term := Required.Term
abbrev Result := PresenceDataInference.Result

def infer (e : Term) : Result :=
  if InferenceSyntax.supported e then PresenceDataInference.infer (Required.decode e)
  else .unsupported

/-- Variables, literals, unannotated lets, pairs/projections, empty records,
records/defaults, field access and variants; malformed operations included. -/
def Data (e : Term) : Prop :=
  InferenceSyntax.supported e = true ∧ PresenceDataInference.Data (Required.decode e)

@[simp] theorem infer_embed (e : Inference.Expr) :
    infer (Required.embed e) = PresenceDataInference.infer e := by simp [infer]

theorem typing_syntax (typed : Presence.Typing Γ e c) : InferenceSyntax.supported e = true := by
  induction typed <;> simp_all [InferenceSyntax.supported]

theorem infer_solved_iff (e : Term) (shape : Shape) :
    infer e = .solved shape ↔ InferenceSyntax.supported e = true ∧
      PresenceDataInference.infer (Required.decode e) = .solved shape := by
  cases valid : InferenceSyntax.supported e <;> simp [infer, valid]

/-- All Core terms and all target predicates; neither solver success nor a
typing derivation is an input hypothesis. No free regular parameters claimed. -/
theorem infer_instances_exact (e : Term) (target : Ty) :
    Typing Presence.model [] e target ↔
      ∃ shape, infer e = .solved shape ∧ Le shape.denote target := by
  change Presence.Typing [] e target ↔ _
  constructor
  · intro typed
    obtain ⟨shape, found, below⟩ :=
      (PresenceDataInference.infer_instances_exact (Required.decode e) target).mp
        (Presence.reflected typed)
    exact ⟨shape, (infer_solved_iff e shape).mpr ⟨typing_syntax typed, found⟩, below⟩
  · rintro ⟨shape, found, below⟩
    obtain ⟨checked, found⟩ := (infer_solved_iff e shape).mp found
    have typed := Presence.preserved
      ((PresenceDataInference.infer_instances_exact (Required.decode e) target).mpr ⟨shape, found, below⟩)
    simpa only [InferenceSyntax.embed_decode e checked] using typed

theorem infer_unsupported_iff (e : Term) : infer e = .unsupported ↔ ¬ Data e := by
  cases checked : InferenceSyntax.supported e with
  | false => simp [infer, Data, checked]
  | true => simpa only [infer, checked, ↓reduceIte, Data, true_and] using
      PresenceDataInference.infer_unsupported_iff (Required.decode e)

theorem data_ne_unsupported (e : Term) (fragment : Data e) : infer e ≠ .unsupported :=
  fun failed => ((infer_unsupported_iff e).mp failed) fragment

theorem infer_rejected_iff (e : Term) : infer e = .rejected ↔
    Data e ∧ ¬ ∃ target, Typing Presence.model [] e target := by
  cases checked : InferenceSyntax.supported e with
  | false => simp [infer, Data, checked]
  | true =>
      have exactTyping (target : Ty) :
          PresenceDataInference.Typing [] (Required.decode e) target ↔
            Typing Presence.model [] e target := by
        simpa only [InferenceSyntax.embed_decode e checked] using
          Presence.conservative [] (Required.decode e) target
      rw [infer, ite_eq_left checked, PresenceDataInference.infer_rejected_iff]
      constructor
      · rintro ⟨data, absent⟩
        exact ⟨⟨checked, data⟩, fun ⟨target, typed⟩ => absent ⟨target, (exactTyping target).mpr typed⟩⟩
      · rintro ⟨⟨_, data⟩, absent⟩
        exact ⟨data, fun ⟨target, typed⟩ => absent ⟨target, (exactTyping target).mp typed⟩⟩

end Yulang.Core.PresenceInference
