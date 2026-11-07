import Yulang.CommonDefaultInspection

/-!
# Finite record-construction inspection against arbitrary targets

The actual compiler emits the explicit head guard, both selected payload
comparisons and the finite remaining-tail checks. Its output contains only
ordinary child subtype obligations. A known-present default is used only in
the proof of this direct decomposition, not as the implementation of the
record inspector.
-/

namespace Yulang.CommonRecordInspection

open CommonPayloadProjection
open CommonDefaultTargetSplit
open CommonDefaultInspection

private theorem bottom_below (target : Common.Ty) : Common.Subtype .bottom target := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs _
  exact CommonFinite.probeAt_bottom rank obs

private theorem profile_union_bottom (payload : Common.Ty) (target : Option Common.Ty) :
    ProfileLe (some (.union payload .bottom)) target ↔ ProfileLe (some payload) target := by
  cases target with
  | none => rfl
  | some target =>
      change Common.Subtype (.union payload .bottom) target ↔ Common.Subtype payload target
      rw [Common.common_union_is_join]
      exact and_iff_left (bottom_below target)

private theorem selectedField_record (label : Nat) (payload rest : Common.Ty) :
    selectedField label (Common.record label payload rest) .bottom =
      some (.union payload .bottom) := by
  simp [selectedField, selectedPayload, optionalProject, Common.record,
    CommonDefaultRequired.present, CommonDefaultRequired.fieldPresence,
    Profile.both, Payload.common, Payload.evalLayer, CommonSyntax.graph]

private theorem selectedOptional_record (label : Nat) (payload rest : Common.Ty) :
    selectedOptional label (Common.record label payload rest) .bottom =
      some (.union payload .bottom) := by
  simp [selectedOptional, selectedPayload, optionalProject, Common.record,
    CommonDefaultRequired.present, CommonDefaultRequired.fieldPresence,
    Profile.both, Profile.withTrivial, Payload.common, Payload.evalLayer, CommonSyntax.graph]

/-- The constructed head is absent from the remaining-tail obligations. -/
theorem record_tail_hidden (label : Nat) (payload rest target : Common.Ty) :
    Common.RecordTailLe [label] (Common.record label payload rest) target ↔
      Common.RecordTailLe [label] rest target := by
  apply forall_congr'
  intro depth
  exact CommonFinite.recordTailLe_hidden_head_iff [] label _ _ _

/-- Every common target reduces to the record head, the actual payload, and
the remaining tail. No shape hypothesis is imposed on the payload or tail. -/
theorem record_target_split (label : Nat) (payload rest target : Common.Ty) :
    Common.Subtype (Common.record label payload rest) target ↔
      CommonRecordEnvelope.outsideRecords target = false ∧
        ProfileLe (some payload) (fieldType [] label target) ∧
        ProfileLe (some payload) (optionalType [] label target) ∧
        Common.RecordTailLe [label] rest target := by
  have same := Common.default_present_record label payload rest .bottom
  have compare : Common.Subtype (Common.record label payload rest) target ↔
      Common.Subtype (Common.recordDefault label (Common.record label payload rest) .bottom) target :=
    ⟨fun below => Common.subtype_trans same.1 below,
      fun below => Common.subtype_trans same.2 below⟩
  rw [compare, default_target_split, selectedField_record, selectedOptional_record,
    profile_union_bottom, profile_union_bottom, record_tail_hidden]

def compileRecord (label : Nat) (payload rest target : Common.Ty) : List Check :=
  [.flag (!CommonRecordEnvelope.outsideRecords target)] ++
  compileProfile (some payload) (fieldType [] label target) ++
  compileProfile (some payload) (optionalType [] label target) ++
  compileTail [label] rest target

theorem compileRecord_exact (label : Nat) (payload rest target : Common.Ty) :
    ChecksHold (compileRecord label payload rest target) ↔
      Common.Subtype (Common.record label payload rest) target := by
  rw [record_target_split]
  simp only [compileRecord, checksHold_append, checksHold_cons, Check.Holds, checksHold_nil,
    and_true, compileProfile_exact, compileTail_exact, and_assoc]
  cases CommonRecordEnvelope.outsideRecords target <;> simp

def inspectRecord (label : Nat) (payload rest target : Common.Ty) : List Branch :=
  match discharge (compileRecord label payload rest target) with
  | none => []
  | some branch => [branch]

/-- A complete finite outer inspector for record construction. The payload,
tail and target may contain arbitrary masks, defaults and regular graphs. -/
theorem record_inspect_exact (label : Nat) (payload rest target : Common.Ty) :
    Common.Subtype (Common.record label payload rest) target ↔
      ∃ branch ∈ inspectRecord label payload rest target, IndependentObligationsHold branch := by
  rw [← compileRecord_exact, discharge_exact]
  cases outcome : discharge (compileRecord label payload rest target) <;>
    simp [inspectRecord, outcome]

def inspectRequired (label : Nat) (payload target : Common.Ty) : List Branch :=
  inspectRecord label payload Common.emptyRecord target

theorem required_inspect_exact (label : Nat) (payload target : Common.Ty) :
    Common.Subtype (Common.required label payload) target ↔
      ∃ branch ∈ inspectRequired label payload target, IndependentObligationsHold branch :=
  record_inspect_exact label payload Common.emptyRecord target

end Yulang.CommonRecordInspection
