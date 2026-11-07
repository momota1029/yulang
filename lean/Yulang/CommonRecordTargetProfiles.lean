import Yulang.CommonRecordTailProfiles

/-!
# Arbitrary common sources against generated record targets

Width-record demands depend exactly on record shape. A single required field
depends exactly on its field profile, including the distinction between an
absent profile and a top payload. The initial constructor cutoff follows from
positive field presence; it is not omitted or assumed by the caller.

These laws hold for arbitrary finite/regular sources, including mixed lattice
heads, outer masks and whole defaults. They supply the record-target cases of
the symbolic source inspector without restricting unknown assignments.
-/

namespace Yulang.CommonRecordTargetProfiles

open Common (Ty Row)
open CommonPayloadProjection (ProfileBelow fieldType)

universe u v

section Finite

variable {R : Type u} {leRow : R → R → Prop} {env : CommonFinite.Environment R}
    {argumentOrder : CommonFinite.Ty R → CommonFinite.Ty R → Prop}

theorem field_implies_records (source : CommonFinite.Ty R) (hidden : List Nat)
    (label : Nat) (obs : CommonFinite.Observation R)
    (accepted : CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source (.field label obs)) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source .records := by
  induction source generalizing hidden with
  | union first last before after => exact ⟨before hidden accepted.1, after hidden accepted.2⟩
  | inter first last before after =>
      exact accepted.elim
        (fun valid => Or.inl (before hidden valid)) (fun valid => Or.inr (after hidden valid))
  | mask more source ih => exact ih (hidden ++ more) accepted
  | bottom | emptyRecord | exactEmpty | record | recordDefault => trivial
  | _ => exact False.elim accepted

theorem records_implies_role (source : CommonFinite.Ty R) (hidden : List Nat) (name : Nat)
    (member : ProducerContextual.Head.records ∈ env.roles name)
    (accepted : CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source .records) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source (.role name) := by
  induction source generalizing hidden with
  | union first last before after => exact ⟨before hidden accepted.1, after hidden accepted.2⟩
  | inter first last before after =>
      exact accepted.elim
        (fun valid => Or.inl (before hidden valid)) (fun valid => Or.inr (after hidden valid))
  | mask more source ih => exact ih (hidden ++ more) accepted
  | bottom => trivial
  | emptyRecord | exactEmpty | record | recordDefault => exact member
  | _ => exact False.elim accepted

theorem field_implies_optional (source : CommonFinite.Ty R) (hidden : List Nat)
    (label : Nat) (obs : CommonFinite.Observation R)
    (accepted : CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source (.field label obs)) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source (.optional label obs) := by
  induction source generalizing hidden with
  | union first last before after => exact ⟨before hidden accepted.1, after hidden accepted.2⟩
  | inter first last before after =>
      exact accepted.elim
        (fun valid => Or.inl (before hidden valid)) (fun valid => Or.inr (after hidden valid))
  | mask more source ih => exact ih (hidden ++ more) accepted
  | bottom => trivial
  | record current payload tail _ ih =>
      by_cases active : label = current ∧ current ∉ hidden
      · simpa only [CommonFinite.MaskedProbeStep, ite_eq_left active] using accepted
      · simp only [CommonFinite.MaskedProbeStep, ite_eq_right active] at accepted ⊢
        exact Or.inl (ih hidden accepted)
  | recordDefault current source fallback ih _ =>
      by_cases active : label = current ∧ current ∉ hidden
      · simp only [CommonFinite.MaskedProbeStep, ite_eq_left active] at accepted ⊢
        exact Or.inl accepted
      · simp only [CommonFinite.MaskedProbeStep, ite_eq_right active] at accepted ⊢
        exact Or.inl (ih hidden accepted)
  | _ => exact False.elim accepted

theorem finite_required_iff (source payload : CommonFinite.Ty R) (label : Nat) :
    CommonFinite.ProducerLe leRow source (CommonFinite.required label payload) ↔
      ∀ rank env obs, CommonFinite.ProbeAt leRow rank env payload obs →
        CommonFinite.ProbeAt leRow rank env source (.field label obs) := by
  constructor
  · intro below rank env obs accepted
    apply (CommonFinite.producerLe_iff_probe _ _).mp below rank env (.field label obs)
    simpa only [CommonFinite.required, CommonFinite.probeAt_record_field, ↓reduceIte] using accepted
  · intro fields
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have recorded : CommonFinite.ProbeAt leRow rank env source .records := by
      have present := fields rank env .trivial (CommonFinite.probeAt_trivial rank payload)
      cases rank <;> exact field_implies_records source [] label .trivial present
    cases obs with
    | trivial => exact CommonFinite.probeAt_trivial rank source
    | records => exact recorded
    | role name => cases rank <;> exact records_implies_role source [] name accepted recorded
    | field current inner =>
        by_cases same : current = label
        · subst current
          apply fields rank env inner
          simpa only [CommonFinite.required, CommonFinite.probeAt_record_field, ↓reduceIte] using accepted
        · simp only [CommonFinite.required, CommonFinite.probeAt_record_field, same, ↓reduceIte] at accepted
          cases rank <;> exact False.elim accepted
    | optional current inner =>
        by_cases same : current = label
        · subst current
          have present := fields rank env inner (by
            simpa only [CommonFinite.required, CommonFinite.probeAt_record_optional, ↓reduceIte] using accepted)
          cases rank <;> exact field_implies_optional source [] label inner present
        · simp only [CommonFinite.required, CommonFinite.probeAt_record_optional, same, ↓reduceIte] at accepted
          have trivial : inner = .trivial := by
            cases rank <;> exact accepted.elim id id
          subst inner
          cases rank <;> exact (CommonDefaultRequired.optional_trivial_iff_records
            leRow env _ [] source current).mpr recorded
    | _ => cases rank <;> exact False.elim accepted

theorem finite_emptyRecord_iff (source : CommonFinite.Ty R) :
    CommonFinite.ProducerLe leRow source .emptyRecord ↔
      ∀ rank env, CommonFinite.ProbeAt leRow rank env source .records := by
  constructor
  · intro below rank env
    apply (CommonFinite.producerLe_iff_probe _ _).mp below rank env .records
    cases rank <;> trivial
  · intro records
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have recorded := records rank env
    cases obs with
    | trivial => exact CommonFinite.probeAt_trivial rank source
    | records => exact recorded
    | role name => cases rank <;> exact records_implies_role source [] name accepted recorded
    | optional current inner =>
        have trivial : inner = .trivial := by cases rank <;> exact accepted
        subst inner
        cases rank <;> exact (CommonDefaultRequired.optional_trivial_iff_records
          leRow env _ [] source current).mpr recorded
    | _ => cases rank <;> exact False.elim accepted

end Finite

theorem presence_initial (hidden : List Nat) (label : Nat) (source : CommonSyntax.Layer R Index)
    (present : CommonDefaultRequired.fieldPresence hidden label source = true) :
    CommonRecordTailProfiles.initialField hidden label source = true := by
  induction source generalizing hidden <;>
    simp_all [CommonDefaultRequired.fieldPresence, CommonRecordTailProfiles.initialField]
  all_goals grind

theorem record_shape_probe (source : Ty) (depth rank : Nat) (env : CommonFinite.Environment Row) :
    CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth source) .records ↔
      CommonDefaultRequired.recordShape source = true := by
  cases rank <;> exact CommonDefaultRequired.recordShape_exact Common.rowLe env _ _ depth [] source

/-- Every common source, including arbitrary regular and masked assignments,
is below width exactly when it accepts the record-shape demand. -/
theorem subtype_emptyRecord_iff (source : Ty) :
    Common.Subtype source Common.emptyRecord ↔ CommonDefaultRequired.recordShape source = true := by
  constructor
  · intro below
    exact (record_shape_probe source 0 0 ⟨fun _ => .bottom, fun _ => []⟩).mp
      ((finite_emptyRecord_iff _).mp (below 0) 0 _)
  · intro shaped depth
    apply (finite_emptyRecord_iff _).mpr
    intro rank env
    exact (record_shape_probe source depth rank env).mpr shaped

/-- No shape or initial-cutoff premise is needed: a nonempty field profile
already forces both. The output is one ordinary extracted-payload comparison. -/
theorem subtype_required_iff (source payload : Ty) (label : Nat) :
    Common.Subtype source (Common.required label payload) ↔
      ProfileBelow (fieldType [] label source) payload := by
  rw [CommonPayloadProjection.profileBelow_exact]
  constructor
  · intro below depth rank env obs accepted
    apply (CommonPayloadProjection.field_type_exact [] label source depth rank env obs).mp
    have projected := (finite_required_iff _ _ label).mp (below (depth + 1)) rank env obs accepted
    simpa only [CommonFinite.maskedProbeAt_nil] using projected
  · intro fields
    have available : CommonDefaultRequired.fieldPresence [] label source = true := by
      let env : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
      have accepts := (CommonPayloadProjection.field_type_exact [] label source 0 0 env .trivial).mpr
        (fields 0 0 env .trivial (CommonFinite.probeAt_trivial 0 _))
      apply (CommonDefaultRequired.present_positive_depth label source 0 0 env).mp
      simpa only [CommonFinite.maskedProbeAt_nil] using accepts
    have initial := presence_initial [] label source available
    intro depth
    apply (finite_required_iff _ _ label).mpr
    intro rank env obs accepted
    cases depth with
    | zero =>
        simpa only [CommonFinite.maskedProbeAt_nil] using
          (CommonRecordTailProfiles.initial_field_exact [] label source rank env obs).mpr initial
    | succ depth =>
        simpa only [CommonFinite.maskedProbeAt_nil] using
          (CommonPayloadProjection.field_type_exact [] label source depth rank env obs).mpr
            (fields depth rank env obs accepted)

end Yulang.CommonRecordTargetProfiles
