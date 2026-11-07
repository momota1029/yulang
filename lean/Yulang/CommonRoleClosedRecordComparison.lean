import Yulang.CommonRoleClosedRecordResidual

/-!
# Closed record comparison at a validated finite field spine

The field labels are known, while every payload is an arbitrary Common type.
For two closed spines with the same visible labels, actual Common subtyping
reduces to the original first payload at each label. This removes a negative
exact-record target by a proved semantic decomposition, rather than feeding
it into a solver grammar that does not support such a target.
-/

namespace Yulang.CommonRoleClosedRecordComparison

open CommonRoleCanonicalRows (Row lookup)
open CommonPatternConcreteRecordTypes (recordTypeOf)
open CommonRoleClosedRecordResidual (field_probe_exact optional_probe_exact)

def SameLabels (first : Row A) (last : Row B) : Prop :=
  ∀ label, (lookup label first).isSome = (lookup label last).isSome

/-- All Common payloads, all constructor depths and negative ranks. Hidden
duplicates are read through the same original first-field lookup. -/
theorem subtype_lookup_exact (firstType : A → Common.Ty) (lastType : B → Common.Ty)
    (first : Row A) (last : Row B) (shape : SameLabels first last) :
    Common.Subtype (recordTypeOf firstType first) (recordTypeOf lastType last) ↔
      ∀ label a b, lookup label first = some a → lookup label last = some b →
        Common.Subtype (firstType a) (lastType b) := by
  constructor
  · intro below label a b firstAt lastAt depth
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank environment observation accepted
    have target := (field_probe_exact lastType last label (depth + 1) rank environment observation).mpr
      ⟨b, lastAt, accepted⟩
    have source := (CommonFinite.producerLe_iff_probe _ _).mp
      (below (depth + 1)) rank environment (.field label observation) target
    obtain ⟨payload, found, valid⟩ :=
      (field_probe_exact firstType first label (depth + 1) rank environment observation).mp source
    have same : payload = a := Option.some.inj (found.symm.trans firstAt)
    subst payload
    exact valid
  · intro payloads depth
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank environment observation accepted
    cases observation with
    | field label observation =>
        obtain ⟨b, found, valid⟩ :=
          (field_probe_exact lastType last label depth rank environment observation).mp accepted
        have present : (lookup label first).isSome = true := by rw [shape label, found]; rfl
        obtain ⟨a, firstAt⟩ := Option.isSome_iff_exists.mp present
        apply (field_probe_exact firstType first label depth rank environment observation).mpr
        refine ⟨a, firstAt, ?_⟩
        exact (CommonFinite.producerLe_iff_probe _ _).mp
          (Common.quote_observe_le (payloads label a b firstAt found) depth)
          rank environment observation valid
    | optional label observation =>
        apply (optional_probe_exact firstType first label depth rank environment observation).mpr
        intro a firstAt
        have present : (lookup label last).isSome = true := by rw [← shape label, firstAt]; rfl
        obtain ⟨b, found⟩ := Option.isSome_iff_exists.mp present
        have valid := (optional_probe_exact lastType last label depth rank environment observation).mp
          accepted b found
        exact (CommonFinite.producerLe_iff_probe _ _).mp
          (Common.quote_observe_le (payloads label a b firstAt found) depth)
          rank environment observation valid
    | _ =>
        cases first <;> cases last <;> cases rank <;>
          simp only [recordTypeOf, Common.record, Common.exactEmpty, Common.observeTy,
            CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep] at accepted ⊢ <;> exact accepted

end Yulang.CommonRoleClosedRecordComparison
