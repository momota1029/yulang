import Yulang.CommonOptionalBound

/-!
# Whole-default required targets as three ordinary subtype branches

Positive field presence is exactly a required field with top payload. The
optional-payload split therefore removes both semantic primitives from a
whole-default comparison. The resulting three branches contain only common
subtype comparisons, preserve the original source and payload sharing, and
use fixed syntax rather than inspecting an instantiated source.

This does not solve the new upper union bounds or prove saturation closure.
-/

namespace Yulang.CommonDefaultBounds

open Common (Ty Row Subtype)
open CommonSyntax (Layer)
open CommonDefaultRequired (present)
open CommonOptionalBound (guardedOptional)
open CommonRecordTargetProfiles

theorem present_iff_required_top (label : Nat) (source : Ty) :
    present label source = true ↔ Subtype source (Common.required label .top) := by
  constructor
  · intro present
    have initial := presence_initial [] label source present
    intro depth
    apply (finite_required_iff _ _ label).mpr
    intro rank env obs accepted
    cases depth with
    | zero =>
        simpa only [CommonFinite.maskedProbeAt_nil] using
          (CommonRecordTailProfiles.initial_field_exact [] label source rank env obs).mpr initial
    | succ depth =>
        have trivial : obs = .trivial := by
          cases obs <;> cases rank <;>
            simp_all [CommonSyntax.observe, CommonSyntax.graph, Layer.evalAt,
              CommonFinite.ProbeAt, CommonFinite.ProbeStep,
              CommonFinite.MaskedProbeStep]
        subst obs
        exact (CommonDefaultRequired.present_positive_depth label source depth rank env).mpr present
  · intro below
    let env : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
    have accepted := (finite_required_iff _ _ label).mp (below 1) 0 env .trivial
      (CommonFinite.probeAt_trivial 0 _)
    exact (CommonDefaultRequired.present_positive_depth label source 0 0 env).mp accepted

/-- All arguments are arbitrary common types. No record-shape, presence,
support, solution, or fuel premise is required. -/
theorem default_required_branches_exact (label : Nat) (source fallback payload : Ty) :
    Subtype (Common.recordDefault label source fallback) (Common.required label payload) ↔
      (Subtype .top payload ∧ Subtype source Common.emptyRecord) ∨
      (Subtype source (guardedOptional label payload) ∧
        Subtype source (Common.required label .top)) ∨
      (Subtype source (guardedOptional label payload) ∧ Subtype fallback payload) := by
  change Common.model.subTy (Common.recordDefault label source fallback)
    (Common.required label payload) ↔ _
  rw [CommonDefaultRequired.default_required_iff]
  constructor
  · rintro ⟨optional, selected⟩
    rcases (CommonOptionalBound.optional_payload_branches_exact label source payload).mp optional with
      top | guarded
    · exact Or.inl top
    · rcases selected with present | fallback
      · exact Or.inr (Or.inl ⟨guarded, (present_iff_required_top label source).mp present⟩)
      · exact Or.inr (Or.inr ⟨guarded, fallback⟩)
  · rintro (top | ⟨guarded, present⟩ | ⟨guarded, fallback⟩)
    · exact ⟨(CommonOptionalBound.optional_payload_branches_exact label source payload).mpr
        (Or.inl top), Or.inr (Common.subtype_trans (CommonBoundCoalescing.le_top fallback) top.1)⟩
    · exact ⟨(CommonOptionalBound.guarded_optional_iff label source payload).mp guarded |>.2,
        Or.inl ((present_iff_required_top label source).mpr present)⟩
    · exact ⟨(CommonOptionalBound.guarded_optional_iff label source payload).mp guarded |>.2,
        Or.inr fallback⟩

end Yulang.CommonDefaultBounds
