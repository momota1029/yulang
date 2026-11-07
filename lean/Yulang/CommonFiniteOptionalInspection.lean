import Yulang.CommonOptionalInspection
import Yulang.CommonFiniteChildInspection

/-!
# Finite observations for required and raw optional bounds

The optional bound is exactly `exactEmpty | required label payload`.
Its payload is guarded, but its selected field/optional observation and
same-depth record tail are not. In particular constructor depth zero is
retained, including the distinction between width and raw optional top.

Default branches use mixed depths: source optional/presence/width edges stay
at the current depth; fallback and top-to-payload edges use one smaller
constructor observation. Local width premises are explicit finite inequalities.
-/

namespace Yulang.CommonFiniteOptionalInspection

open Common (Ty Row)
open CommonFiniteChildInspection (BelowAt GuardedAt)
open CommonOptionalBound (guardedOptional)

theorem required_at_iff (depth : Nat) (source payload : Ty) (label : Nat) :
    BelowAt depth source (Common.required label payload) ↔
      ∀ rank env obs,
        CommonFinite.ProbeAt Common.rowLe rank env
          (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node payload)) obs →
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) (.field label obs) :=
  CommonRecordTargetProfiles.finite_required_iff _ _ _

theorem optional_at_iff (depth : Nat) (source payload : Ty) (label : Nat) :
    BelowAt depth source (guardedOptional label payload) ↔
      ∀ rank env obs,
        CommonFinite.ProbeAt Common.rowLe rank env
          (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node payload)) obs →
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) (.optional label obs) :=
  CommonOptionalBound.finite_optional_iff _ _ _

theorem width_optional_trivial_at (depth : Nat) (source : Ty)
    (width : BelowAt depth source Common.emptyRecord)
    (rank : Nat) (env : CommonFinite.Environment Row) (label : Nat) :
    CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) (.optional label .trivial) := by
  apply (CommonFinite.producerLe_iff_probe _ _).mp width rank env (.optional label .trivial)
  cases rank <;> rfl

theorem record_same_required_at_iff (depth label : Nat) (head tail payload : Ty) :
    BelowAt depth (Common.record label head tail) (Common.required label payload) ↔
      GuardedAt depth head payload :=
  CommonFinite.singleton_requirement_iff label _ _ _

theorem record_same_optional_at_iff (depth label : Nat) (head tail payload : Ty) :
    BelowAt depth (Common.record label head tail) (guardedOptional label payload) ↔
      GuardedAt depth head payload := by
  rw [optional_at_iff]
  change (∀ rank env obs, CommonFinite.ProbeAt _ rank env _ obs →
    CommonFinite.ProbeAt _ rank env (.record label _ _) (.optional label obs)) ↔ _
  simp only [CommonFinite.probeAt_record_optional, ↓reduceIte]
  exact (CommonFinite.producerLe_iff_probe _ _).symm

theorem record_other_required_at_iff (depth current label : Nat) (head tail payload : Ty)
    (different : label ≠ current) :
    BelowAt depth (Common.record current head tail) (Common.required label payload) ↔
      BelowAt depth tail (Common.required label payload) := by
  rw [required_at_iff, required_at_iff]
  change (∀ rank env obs, CommonFinite.ProbeAt _ rank env _ obs →
    CommonFinite.ProbeAt _ rank env (.record current _ _) (.field label obs)) ↔ _
  simp only [CommonFinite.probeAt_record_field, different, ↓reduceIte]
  rfl

theorem record_other_optional_at_iff (depth current label : Nat) (head tail payload : Ty)
    (different : label ≠ current) (width : BelowAt depth tail Common.emptyRecord) :
    BelowAt depth (Common.record current head tail) (guardedOptional label payload) ↔
      BelowAt depth tail (guardedOptional label payload) := by
  rw [optional_at_iff, optional_at_iff]
  constructor
  · intro selected rank env obs accepted
    have probe := selected rank env obs accepted
    change CommonFinite.ProbeAt _ rank env (.record current _ _) (.optional label obs) at probe
    rw [CommonFinite.probeAt_record_optional] at probe
    simp only [different, ↓reduceIte] at probe
    exact probe.elim id (fun same => same ▸ width_optional_trivial_at depth tail width rank env label)
  · intro selected rank env obs accepted
    change CommonFinite.ProbeAt _ rank env (.record current _ _) (.optional label obs)
    rw [CommonFinite.probeAt_record_optional]
    simp only [different, ↓reduceIte]
    exact Or.inl (selected rank env obs accepted)

theorem default_other_required_at_iff (depth current label : Nat) (source fallback payload : Ty)
    (different : label ≠ current) :
    BelowAt depth (Common.recordDefault current source fallback) (Common.required label payload) ↔
      BelowAt depth source (Common.required label payload) := by
  rw [required_at_iff, required_at_iff]
  cases depth with
  | zero =>
      change (∀ rank env obs, CommonFinite.ProbeAt _ rank env _ obs →
        CommonFinite.ProbeAt _ rank env (.record current _ _) (.field label obs)) ↔ _
      simp only [CommonFinite.probeAt_record_field, different, ↓reduceIte]
      rfl
  | succ depth =>
      change (∀ rank env obs, CommonFinite.ProbeAt _ rank env _ obs →
        CommonFinite.ProbeAt _ rank env (.recordDefault current _ _) (.field label obs)) ↔ _
      simp only [CommonFinite.probeAt_default_field, different, ↓reduceIte]
      rfl

theorem default_other_optional_at_iff (depth current label : Nat) (source fallback payload : Ty)
    (different : label ≠ current) (width : BelowAt depth source Common.emptyRecord) :
    BelowAt depth (Common.recordDefault current source fallback) (guardedOptional label payload) ↔
      BelowAt depth source (guardedOptional label payload) := by
  have same (rank : Nat) (env : CommonFinite.Environment Row) (obs : Common.Observation) :
      CommonFinite.ProbeAt Common.rowLe rank env
          (Common.observeTy depth (Common.recordDefault current source fallback)) (.optional label obs) ↔
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) (.optional label obs) := by
    have finish :
        (CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) (.optional label obs) ∨
          obs = .trivial) ↔
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) (.optional label obs) :=
      ⟨fun valid => valid.elim id (fun equal => equal ▸ width_optional_trivial_at depth source width rank env label),
        Or.inl⟩
    cases depth with
    | zero =>
        change CommonFinite.ProbeAt _ rank env (.record current _ _) (.optional label obs) ↔ _
        simpa only [CommonFinite.probeAt_record_optional, different, ↓reduceIte, Common.observeTy] using finish
    | succ depth =>
        change CommonFinite.ProbeAt _ rank env (.recordDefault current _ _) (.optional label obs) ↔ _
        simpa only [CommonFinite.probeAt_default_optional, different, ↓reduceIte, Common.observeTy] using finish
  simp only [optional_at_iff, same]

theorem optional_at_implies_width (depth label : Nat) (source payload : Ty)
    (below : BelowAt depth source (guardedOptional label payload)) :
    BelowAt depth source Common.emptyRecord := by
  have targetWidth : Common.Subtype (guardedOptional label payload) Common.emptyRecord := by
    apply (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr
    rfl
  exact CommonFinite.producerLe_trans below (targetWidth depth)

/-- Soundness needs no separate width premise: the emitted optional child
edge itself supplies width at the observation being proved. -/
theorem record_other_optional_at_sound (depth current label : Nat) (head tail payload : Ty)
    (different : label ≠ current) (below : BelowAt depth tail (guardedOptional label payload)) :
    BelowAt depth (Common.record current head tail) (guardedOptional label payload) :=
  (record_other_optional_at_iff depth current label head tail payload different
    (optional_at_implies_width depth label tail payload below)).mpr below

theorem default_other_optional_at_sound (depth current label : Nat) (source fallback payload : Ty)
    (different : label ≠ current) (below : BelowAt depth source (guardedOptional label payload)) :
    BelowAt depth (Common.recordDefault current source fallback) (guardedOptional label payload) :=
  (default_other_optional_at_iff depth current label source fallback payload different
    (optional_at_implies_width depth label source payload below)).mpr below

theorem default_zero_required (label : Nat) (source fallback payload : Ty) :
    BelowAt 0 (Common.recordDefault label source fallback) (Common.required label payload) :=
  (CommonFinite.singleton_requirement_iff label _ _ _).mpr (CommonFinite.producerLe_refl _)

theorem default_zero_optional (label : Nat) (source fallback payload : Ty) :
    BelowAt 0 (Common.recordDefault label source fallback) (guardedOptional label payload) :=
  CommonFinite.producerLe_trans (default_zero_required label source fallback payload)
    (CommonBoundCoalescing.le_union_right Common.exactEmpty (Common.required label payload) 0)

theorem default_same_at_iff (depth label : Nat) (source fallback payload : Ty)
    (width : BelowAt depth source Common.emptyRecord) :
    BelowAt depth (Common.recordDefault label source fallback) (guardedOptional label payload) ↔
      BelowAt depth (Common.recordDefault label source fallback) (Common.required label payload) := by
  constructor
  · intro below
    cases depth with
    | zero => exact default_zero_required label source fallback payload
    | succ depth =>
        apply (required_at_iff (depth + 1) _ _ label).mpr
        intro rank env obs accepted
        have selected := (optional_at_iff (depth + 1) _ _ label).mp below rank env obs accepted
        change CommonFinite.ProbeAt _ rank env (.recordDefault label _ _) (.optional label obs) at selected
        rw [CommonFinite.probeAt_default_optional] at selected
        simp only [↓reduceIte] at selected
        change CommonFinite.ProbeAt _ rank env (.recordDefault label _ _) (.field label obs)
        rw [CommonFinite.probeAt_default_field]
        simp only [↓reduceIte]
        rcases selected with selected | rfl
        · exact selected
        · exact ⟨width_optional_trivial_at _ source width rank env label,
            Or.inr (CommonFinite.probeAt_trivial rank _)⟩
  · intro below
    exact CommonFinite.producerLe_trans below
      (CommonBoundCoalescing.le_union_right Common.exactEmpty (Common.required label payload) depth)

/-- The same fixed three alternatives as the symbolic compiler, with the
constructor-depth shifts made explicit. -/
def DefaultBranchesAt (depth label : Nat) (source fallback payload : Ty) : Prop :=
  (GuardedAt depth .top payload ∧ BelowAt depth source Common.emptyRecord) ∨
    (BelowAt depth source (guardedOptional label payload) ∧
      BelowAt depth source (Common.required label .top)) ∨
    (BelowAt depth source (guardedOptional label payload) ∧ GuardedAt depth fallback payload)

private theorem top_probe_trivial (rank : Nat) (env : CommonFinite.Environment Row)
    (obs : Common.Observation) (accepted : CommonFinite.ProbeAt Common.rowLe rank env .top obs) :
    obs = .trivial := by
  cases rank <;> cases obs <;>
    simp_all [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

/-- Every selected branch is sound at every observation. No local width
premise is required for this direction; width is explicit in the first branch. -/
theorem default_branches_at_sound (depth label : Nat) (source fallback payload : Ty)
    (selected : DefaultBranchesAt depth label source fallback payload) :
    BelowAt depth (Common.recordDefault label source fallback) (Common.required label payload) := by
  cases depth with
  | zero => exact default_zero_required label source fallback payload
  | succ depth =>
      apply (CommonDefaultRequired.finite_default_required_iff Common.rowLe label _ _ _).mpr
      intro rank env obs accepted
      rcases selected with ⟨top, width⟩ | ⟨optional, present⟩ | ⟨optional, fallback⟩
      · have trivial := top_probe_trivial rank env obs ((CommonFinite.producerLe_iff_probe _ _).mp top rank env obs accepted)
        subst obs
        exact ⟨width_optional_trivial_at _ source width rank env label,
          Or.inr (CommonFinite.probeAt_trivial rank _)⟩
      · exact ⟨(optional_at_iff (depth + 1) source payload label).mp optional rank env obs accepted,
          Or.inl ((required_at_iff (depth + 1) source .top label).mp present rank env .trivial
            (CommonFinite.probeAt_trivial rank _))⟩
      · exact ⟨(optional_at_iff (depth + 1) source payload label).mp optional rank env obs accepted,
          Or.inr ((CommonFinite.producerLe_iff_probe _ _).mp fallback rank env obs accepted)⟩

theorem default_branches_optional_at_sound (depth label : Nat) (source fallback payload : Ty)
    (selected : DefaultBranchesAt depth label source fallback payload) :
    BelowAt depth (Common.recordDefault label source fallback) (guardedOptional label payload) :=
  CommonFinite.producerLe_trans (default_branches_at_sound depth label source fallback payload selected)
    (CommonBoundCoalescing.le_union_right Common.exactEmpty (Common.required label payload) depth)

theorem width_not_raw_optional_at_zero (label : Nat) (payload : Ty) :
    ¬ BelowAt 0 Common.emptyRecord (guardedOptional label payload) := by
  intro below
  have impossible := (optional_at_iff 0 Common.emptyRecord payload label).mp below
    0 ⟨fun _ => .bottom, fun _ => []⟩ .impossible (by trivial)
  cases impossible

/-- At depth zero even a top payload has the raw optional field requirement.
Replacing this target by width would therefore change the finite semantics. -/
theorem raw_optional_top_zero_differs_from_width (label : Nat) :
    BelowAt 0 Common.emptyRecord Common.emptyRecord ∧
      ¬ BelowAt 0 Common.emptyRecord (guardedOptional label .top) :=
  ⟨CommonFinite.producerLe_refl _, width_not_raw_optional_at_zero label .top⟩

theorem default_zero_branches_need_width (label : Nat) (fallback payload : Ty) :
    BelowAt 0 (Common.recordDefault label (.base .int) fallback) (Common.required label payload) ∧
      ¬ DefaultBranchesAt 0 label (.base .int) fallback payload := by
  refine ⟨default_zero_required label _ fallback payload, ?_⟩
  intro selected
  have noWidth : ¬ BelowAt 0 (.base .int) Common.emptyRecord := by
    intro width
    have impossible := (CommonRecordTargetProfiles.finite_emptyRecord_iff _).mp width
      0 ⟨fun _ => .bottom, fun _ => []⟩
    exact impossible
  have noOptional : ¬ BelowAt 0 (.base .int) (guardedOptional label payload) := by
    intro optional
    have impossible := (optional_at_iff 0 (.base .int) payload label).mp optional
      0 ⟨fun _ => .bottom, fun _ => []⟩ .trivial (CommonFinite.probeAt_trivial 0 _)
    exact impossible
  exact selected.elim (fun branch => noWidth branch.2)
    (fun branches => branches.elim (fun branch => noOptional branch.1) (fun branch => noOptional branch.1))

end Yulang.CommonFiniteOptionalInspection
