import Yulang.CommonRoleCanonicalRows
import Yulang.CommonPatternConcreteRecordTypes

/-!
# Canonical subtraction for exact finite Common record spines

Unlike the width-ended record encoding, this component preserves the
`exactEmpty` terminal of a closed source spine. The payload interpretation is
arbitrary Common syntax, including regular graphs. Normalization removes
hidden duplicate fields according to Common's actual first-field rule.

Physical subtraction is not identified with an outer producer mask: a mask
forgets the removed label's absence, whereas the closed residual knows it.
Pending source spines and role candidate selection remain separate work.
-/

namespace Yulang.CommonRoleClosedRecordResidual

open CommonRoleCanonicalRows (Row normalize residual capture lookup)
open CommonPatternConcreteRecordTypes (recordTypeOf)

/-- Canonical first-field normalization preserves every Common observation,
including known absence and arbitrary nested payload observations. -/
theorem normalize_equivalent (type : Payload → Common.Ty) (fields : Row Payload) :
    Common.Equivalent (recordTypeOf type (normalize fields)) (recordTypeOf type fields) := by
  induction fields with
  | nil => exact Common.equivalent_refl _
  | cons entry rest ih =>
      rcases entry with ⟨label, payload⟩
      simp only [normalize, recordTypeOf]
      have remove := CommonPatternConcreteRecordTypes.insert_filter_exact
        type label payload (normalize rest)
      have filtered : residual [label] (normalize rest) =
          (normalize rest).filter (fun entry => entry.1 != label) := by
        apply List.filter_congr
        intro entry _
        by_cases same : entry.1 = label <;> simp [same]
      rw [filtered]
      exact Common.equivalent_trans remove
        (CommonPatternConcreteRecordTypes.record_congr label
          (Common.equivalent_refl _) ih)

/-- A required observation reads the original first field at every
constructor depth and every negative rank, with the same environment. -/
theorem field_probe_exact (type : Payload → Common.Ty) (fields : Row Payload)
    (label depth rank : Nat) (environment : CommonFinite.Environment Common.Row)
    (observation : CommonFinite.Observation Common.Row) :
    CommonFinite.ProbeAt Common.rowLe rank environment
        (Common.observeTy depth (recordTypeOf type fields)) (.field label observation) ↔
      ∃ payload, lookup label fields = some payload ∧
        CommonFinite.ProbeAt Common.rowLe rank environment
          (CommonSyntax.observe (CommonSyntax.graph Common.Row) depth (.node (type payload)))
          observation := by
  induction fields with
  | nil =>
      cases rank <;> simp [lookup, recordTypeOf, Common.exactEmpty, Common.observeTy,
        CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
        CommonFinite.MaskedProbeStep]
  | cons entry rest ih =>
      rcases entry with ⟨current, item⟩
      simp only [recordTypeOf, Common.record, Common.observeTy, CommonSyntax.Layer.evalAt,
        CommonFinite.probeAt_record_field]
      by_cases same : label = current
      · subst current
        simp [lookup]
      · simpa only [Common.observeTy, lookup, same, ite_false] using ih

/-- A missing field in a closed spine satisfies every optional payload
observation. A present field tests exactly its original first payload. -/
theorem optional_probe_exact (type : Payload → Common.Ty) (fields : Row Payload)
    (label depth rank : Nat) (environment : CommonFinite.Environment Common.Row)
    (observation : CommonFinite.Observation Common.Row) :
    CommonFinite.ProbeAt Common.rowLe rank environment
        (Common.observeTy depth (recordTypeOf type fields)) (.optional label observation) ↔
      ∀ payload, lookup label fields = some payload →
        CommonFinite.ProbeAt Common.rowLe rank environment
          (CommonSyntax.observe (CommonSyntax.graph Common.Row) depth (.node (type payload)))
          observation := by
  induction fields with
  | nil =>
      cases rank <;> simp [lookup, recordTypeOf, Common.exactEmpty, Common.observeTy,
        CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
        CommonFinite.MaskedProbeStep]
  | cons entry rest ih =>
      rcases entry with ⟨current, item⟩
      simp only [recordTypeOf, Common.record, Common.observeTy, CommonSyntax.Layer.evalAt,
        CommonFinite.probeAt_record_optional]
      by_cases same : label = current
      · subst current
        simp [lookup]
      · simp only [lookup, same, ite_false]
        change (CommonFinite.ProbeAt Common.rowLe rank environment
          (Common.observeTy depth (recordTypeOf type rest)) (.optional label observation) ∨
          observation = .trivial) ↔ _
        rw [ih]
        constructor
        · rintro (valid | trivial)
          · exact valid
          · intro payload _
            subst observation
            exact CommonFinite.probeAt_trivial rank _
        · exact Or.inl

theorem capture_lookup (labels : List Nat) (fields : Row Payload) (label : Nat) :
    lookup label (capture labels fields) =
      if label ∈ labels then none else lookup label fields := by
  rw [capture, CommonRoleCanonicalRows.lookup_residual,
    CommonRoleCanonicalRows.lookup_normalize]

/-- The computed closed residual reads exactly the original unremoved
first fields. In particular, no removed label can reappear from a duplicate. -/
theorem capture_field_probe_exact (type : Payload → Common.Ty) (labels : List Nat)
    (fields : Row Payload) (label depth rank : Nat)
    (environment : CommonFinite.Environment Common.Row)
    (observation : CommonFinite.Observation Common.Row) :
    CommonFinite.ProbeAt Common.rowLe rank environment
        (Common.observeTy depth (recordTypeOf type (capture labels fields)))
        (.field label observation) ↔
      label ∉ labels ∧ ∃ payload, lookup label fields = some payload ∧
        CommonFinite.ProbeAt Common.rowLe rank environment
          (CommonSyntax.observe (CommonSyntax.graph Common.Row) depth (.node (type payload)))
          observation := by
  rw [field_probe_exact, capture_lookup]
  by_cases removed : label ∈ labels <;> simp [removed]

end Yulang.CommonRoleClosedRecordResidual
