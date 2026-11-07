import Yulang.CommonLegacyEmptyReflection

/-!
# Why legacy witness recovery cannot use one two-sided erasure

Exact empty and width have the same upper comparisons against all embedded
legacy targets, while width is not below exact empty. Consequently no single
legacy value can simultaneously represent exact empty in both operand
positions of an arbitrary subtype comparison with an old value.

This excludes a tempting uniform witness-erasure proof. It is not a
counterexample to legacy-source reflection: that theorem only needs a
simultaneous assignment satisfying one generated finite constraint problem,
with its requested old result fixed. Such an assignment may depend on that
whole problem and need not preserve every unrelated comparison.
-/

namespace Yulang.CommonLegacyErasureBoundary

open CommonLegacyEmptyReflection (legacyModel contextualModel)

/-- No candidate old value has exact empty's comparisons with all old
values in both the source and the target position. -/
theorem exactEmpty_no_two_sided_legacy_image (candidate : legacyModel.Ty)
    (positive : ∀ target : legacyModel.Ty,
      Common.Subtype Common.exactEmpty (Common.embedOld target) ↔
        contextualModel.subTy candidate target)
    (negative : ∀ source : legacyModel.Ty,
      Common.Subtype (Common.embedOld source) Common.exactEmpty ↔
        contextualModel.subTy source candidate) : False := by
  have reflexive : contextualModel.subTy candidate candidate :=
    (Common.contextual_embedding_exact candidate candidate).mp (Common.subtype_refl _)
  have exactBelow : Common.Subtype Common.exactEmpty (Common.embedOld candidate) :=
    (positive candidate).mpr reflexive
  have widthBelow : contextualModel.subTy .emptyRecord candidate :=
    (CommonLegacyEmptyReflection.exact_empty_upper_contextual_iff candidate).mp exactBelow
  have impossible := (negative .emptyRecord).mpr widthBelow
  exact CommonFinite.width_not_below_exactEmpty (impossible 0)

/-- There is no total erasure that is exact against every old target and
every old source at once. No computability or constructor law is assumed. -/
theorem no_uniform_two_sided_erasure :
    ¬ ∃ erase : Common.Ty → legacyModel.Ty,
      (∀ (source : Common.Ty) (target : legacyModel.Ty),
        Common.Subtype source (Common.embedOld target) ↔
          contextualModel.subTy (erase source) target) ∧
      (∀ (source : legacyModel.Ty) (target : Common.Ty),
        Common.Subtype (Common.embedOld source) target ↔
          contextualModel.subTy source (erase target)) := by
  rintro ⟨erase, positive, negative⟩
  exact exactEmpty_no_two_sided_legacy_image (erase Common.exactEmpty)
    (positive Common.exactEmpty) (fun source => negative source Common.exactEmpty)

end Yulang.CommonLegacyErasureBoundary
