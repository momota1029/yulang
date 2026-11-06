import Yulang.CommonDefault

/-!
# Presence alone does not justify erasing a common whole default

Free intersections can combine exact absence information and required-field
information from different producers. Default inspection must preserve both
the optional-payload test and the presence test. Its known-record rewrite
cannot be generalized to an arbitrary producer merely below a required type.
This is a boundary of demand inspection, separate from runtime inhabitation.
-/

namespace Yulang.CommonDefaultBoundary

open Common

def mixedSource (label : Nat) : Ty := .inter exactEmpty (required label (.base .int))

private def environment : Environment :=
  ⟨fun _ => .finite .bottom, fun _ => []⟩

private theorem finite_int_below_top :
    CommonFinite.ProducerLe rowLe (.base .int) .top := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

/-- Every label gives a source satisfying the ordinary record-shape premise. -/
theorem mixed_source_below_width (label : Nat) : model.subTy (mixedSource label) emptyRecord := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  apply (CommonFinite.probeAt_inter rank _ _ obs).mpr
  exact .inl ((CommonFinite.producerLe_iff_probe _ _).mp
    (CommonFinite.exactEmpty_below_width (leRow := rowLe)) rank env obs accepted)

/-- Presence of the selected field is guaranteed in the same common order. -/
theorem mixed_source_below_required (label : Nat) :
    model.subTy (mixedSource label) (required label .top) := by
  have payloadBound : Subtype (.base .int) .top := fun _ => finite_int_below_top
  intro depth
  have requiredBound := CommonFinite.producerLe_record_mono label
    (quote_observe_le payloadBound depth) (CommonFinite.producerLe_refl (observeTy depth emptyRecord))
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  apply (CommonFinite.probeAt_inter rank _ _ obs).mpr
  exact .inr ((CommonFinite.producerLe_iff_probe _ _).mp requiredBound rank env obs accepted)

/-- The whole default has a string-field observation obtained by combining
the exact-empty optional observation with the other summand's presence. -/
theorem default_accepts_string_field (label : Nat) :
    AcceptAt 1 0 environment (recordDefault label (mixedSource label) .top)
      (.atom (.field label (.base .str))) := by
  simp [AcceptAt, recordDefault, mixedSource, exactEmpty, required, record, emptyRecord,
    observeTy, CommonSyntax.Layer.evalAt, CommonSyntax.observe, CommonSyntax.graph,
    CommonFinite.AcceptAt, CommonFinite.Demand.tests, CommonFinite.ProbeAt,
    CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

theorem source_rejects_string_field (label : Nat) :
    ¬ AcceptAt 1 0 environment (mixedSource label) (.atom (.field label (.base .str))) := by
  simp [AcceptAt, mixedSource, exactEmpty, required, record, emptyRecord,
    observeTy, CommonSyntax.Layer.evalAt, CommonSyntax.observe, CommonSyntax.graph,
    CommonFinite.AcceptAt, CommonFinite.Demand.tests, CommonFinite.ProbeAt,
    CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

/-- Thus even a source below both width and a required field need not be
demand-equivalent to its default extension. No runtime inhabitant is assumed. -/
theorem presence_does_not_erase_default (label : Nat) :
    ¬ Equivalent (recordDefault label (mixedSource label) .top) (mixedSource label) := by
  intro same
  have accepted := (common_subtype_exact _ _).mp same.2 1 0 environment
    (.atom (.field label (.base .str))) (default_accepts_string_field label)
  exact source_rejects_string_field label accepted

end Yulang.CommonDefaultBoundary
