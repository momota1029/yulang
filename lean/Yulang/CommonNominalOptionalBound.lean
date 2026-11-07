import Yulang.CommonNominalRecordTargetProfiles
import Yulang.CommonNominalTypeBounds

/-! Exact optional bounds for arbitrary new regular payloads, using finite
ordinary subtype branches rather than an external top/compatibility test. -/

namespace Yulang.CommonNominalOptionalBound

open CommonNominalCarrier (Ty Row Subtype Equivalent)
open CommonNominalSyntax (Layer)
open CommonNominalDefaultRequired (OptionalPayload)
open CommonNominalRecordTailProfiles (initialOptional)
open CommonNominalRecordTargetProfiles

universe u v

section Finite

variable {R : Type u} {leRow : R → R → Prop}

theorem finite_optional_iff (source payload : CommonNominalFinite.Ty R) (label : Nat) :
    CommonNominalFinite.ProducerLe leRow source (.union .exactEmpty (CommonNominalFinite.required label payload)) ↔
      ∀ rank env obs, CommonNominalFinite.ProbeAt leRow rank env payload obs →
        CommonNominalFinite.ProbeAt leRow rank env source (.optional label obs) := by
  constructor
  · intro below rank env obs accepted
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mp below rank env (.optional label obs)
    rw [CommonNominalFinite.probeAt_union]
    constructor
    · cases rank <;> exact Or.inl (by simp)
    · simpa only [CommonNominalFinite.required, CommonNominalFinite.probeAt_record_optional, ↓reduceIte] using accepted
  · intro selected
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have recorded : CommonNominalFinite.ProbeAt leRow rank env source .records := by
      have trivial := selected rank env .trivial (CommonNominalFinite.probeAt_trivial rank payload)
      cases rank <;> exact (CommonNominalDefaultRequired.optional_trivial_iff_records
        leRow env _ [] source label).mp trivial
    have both := (CommonNominalFinite.probeAt_union rank _ _ obs).mp accepted
    cases obs with
    | trivial => exact CommonNominalFinite.probeAt_trivial rank source
    | records => exact recorded
    | role name => cases rank <;> exact records_implies_role source [] name both.1 recorded
    | optional current inner =>
        have required := both.2
        by_cases same : current = label
        · subst current
          apply selected rank env inner
          simpa only [CommonNominalFinite.required, CommonNominalFinite.probeAt_record_optional, ↓reduceIte] using required
        · simp only [CommonNominalFinite.required, CommonNominalFinite.probeAt_record_optional, same, ↓reduceIte] at required
          have trivial : inner = .trivial := by
            cases rank <;> exact required.elim id id
          subst inner
          cases rank <;> exact (CommonNominalDefaultRequired.optional_trivial_iff_records
            leRow env _ [] source current).mpr recorded
    | _ => cases rank <;> exact False.elim both.1

end Finite

/-- Any nontrivial positive-depth optional observation already forces the
initial Boolean observation. The converse is intentionally not asserted. -/
theorem optional_positive_initial {R : Type u} {Index : Type v}
    (leRow : R → R → Prop) (env : CommonNominalFinite.Environment R)
    (argumentOrder : CommonNominalFinite.Ty R → CommonNominalFinite.Ty R → Prop)
    (assignment : Index → CommonNominalFinite.Ty R) (depth : Nat)
    (hidden : List Nat) (label : Nat) (source : Layer R Index)
    (obs : CommonNominalFinite.Observation R) (notTrivial : obs ≠ .trivial)
    (accepted : CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden
      (source.evalAt (depth + 1) assignment) (.optional label obs)) :
    initialOptional hidden label source = true := by
  induction source generalizing hidden with
  | bottom => rfl
  | union first last before after =>
      simp only [initialOptional, Bool.and_eq_true]
      exact ⟨before hidden accepted.1, after hidden accepted.2⟩
  | inter first last before after =>
      simp only [initialOptional, Bool.or_eq_true]
      exact accepted.elim
        (fun valid => Or.inl (before hidden valid)) (fun valid => Or.inr (after hidden valid))
  | mask more source ih => exact ih (hidden ++ more) accepted
  | record current payload rest ih =>
      by_cases active : label = current ∧ current ∉ hidden
      · simp [initialOptional, active]
      · simp only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, active, ↓reduceIte] at accepted
        simpa only [initialOptional, active, ↓reduceIte] using
          ih hidden (accepted.resolve_right notTrivial)
  | recordDefault current source fallback ih =>
      by_cases active : label = current ∧ current ∉ hidden
      · simp [initialOptional, active]
      · simp only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, active, ↓reduceIte] at accepted
        simpa only [initialOptional, active, ↓reduceIte] using
          ih hidden (accepted.resolve_right notTrivial)
  | exactEmpty =>
      simpa only [initialOptional, decide_eq_true_eq] using accepted.resolve_right notTrivial
  | emptyRecord => exact False.elim (notTrivial accepted)
  | _ => exact False.elim accepted

theorem optional_payload_shape (label : Nat) (source payload : Ty)
    (selected : OptionalPayload label source payload) :
    CommonNominalDefaultRequired.recordShape source = true := by
  let env : CommonNominalFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have trivial := selected 0 0 env .trivial (CommonNominalFinite.probeAt_trivial 0 _)
  have shaped := (CommonNominalDefaultRequired.optional_trivial_iff_records
    Common.rowLe env _ [] (CommonNominalCarrier.observeTy 1 source) label).mp trivial
  exact (record_shape_probe source 1 0 env).mp shaped

def guardedOptional (label : Nat) (payload : Ty) : Ty :=
  .union CommonNominalCarrier.exactEmpty (CommonNominalCarrier.required label payload)

theorem guarded_optional_iff (label : Nat) (source payload : Ty) :
    Subtype source (guardedOptional label payload) ↔
      initialOptional [] label source = true ∧ OptionalPayload label source payload := by
  constructor
  · intro below
    constructor
    · let env : CommonNominalFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
      have accepted := (finite_optional_iff (CommonNominalCarrier.observeTy 0 source) .bottom label).mp
        (below 0) 0 env .impossible (by trivial)
      exact (CommonNominalRecordTailProfiles.initial_optional_exact [] label source 0 env
        .impossible (by intro impossible; cases impossible)).mp accepted
    · intro depth rank env obs accepted
      exact (finite_optional_iff _ _ label).mp (below (depth + 1)) rank env obs accepted
  · rintro ⟨initial, selected⟩
    have shaped := optional_payload_shape label source payload selected
    intro depth
    apply (finite_optional_iff _ _ label).mpr
    intro rank env obs accepted
    cases depth with
    | zero =>
        by_cases trivial : obs = .trivial
        · subst obs
          have recorded := (record_shape_probe source 0 rank env).mpr shaped
          cases rank <;> exact (CommonNominalDefaultRequired.optional_trivial_iff_records
            Common.rowLe env _ [] (CommonNominalCarrier.observeTy 0 source) label).mpr recorded
        · simpa only [CommonNominalFinite.maskedProbeAt_nil] using
            (CommonNominalRecordTailProfiles.initial_optional_exact [] label source rank env obs trivial).mpr initial
    | succ depth => exact selected depth rank env obs accepted


/-- A proof-only witness of failure of top subtyping. No finite root role
test, compatibility oracle or negative condition is returned by a compiler. -/
theorem not_top_witness (payload : Ty) (notTop : ¬ Subtype .top payload) :
    ∃ (depth rank : Nat) (env : CommonNominalFinite.Environment Row) (obs : CommonNominalFinite.Observation Row),
      CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth payload) obs ∧
        obs ≠ .trivial := by
  apply Classical.byContradiction
  intro absent
  apply notTop
  intro depth
  apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  by_cases trivial : obs = .trivial
  · subst obs
    exact CommonNominalFinite.probeAt_trivial rank _
  · exact False.elim (absent ⟨depth, rank, env, obs, accepted, trivial⟩)

theorem optional_payload_initial (label : Nat) (source payload : Ty)
    (notTop : ¬ Subtype .top payload) (selected : OptionalPayload label source payload) :
    initialOptional [] label source = true := by
  obtain ⟨depth, rank, env, obs, accepted, notTrivial⟩ := not_top_witness payload notTop
  have sourceAccepted := selected depth rank env obs accepted
  cases rank <;>
    exact optional_positive_initial Common.rowLe env _ _ depth [] label source obs notTrivial sourceAccepted

theorem optional_payload_top_iff (label : Nat) (source payload : Ty) (topBelow : Subtype .top payload) :
    OptionalPayload label source payload ↔ Subtype source CommonNominalCarrier.emptyRecord := by
  constructor
  · intro selected
    exact (subtype_emptyRecord_iff source).mpr (optional_payload_shape label source payload selected)
  · intro width depth rank env obs accepted
    have top := (CommonNominalFinite.producerLe_iff_probe _ _).mp (topBelow depth) rank env obs accepted
    have trivial : obs = .trivial := by
      cases obs <;> cases rank <;> simp_all [CommonNominalCarrier.observeTy, Layer.evalAt,
        CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep]
    subst obs
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mp (width (depth + 1)) rank env (.optional label .trivial)
    cases rank <;> rfl

/-- An executable finite branch list can contain just these ordinary
comparisons. Classical top/non-top reasoning is confined to this proof of
completeness, not an executable subtype decision or a parameter guard. -/
theorem optional_payload_branches_exact (label : Nat) (source payload : Ty) :
    OptionalPayload label source payload ↔
      (Subtype .top payload ∧ Subtype source CommonNominalCarrier.emptyRecord) ∨
        Subtype source (guardedOptional label payload) := by
  constructor
  · intro selected
    by_cases top : Subtype .top payload
    · exact Or.inl ⟨top, (optional_payload_top_iff label source payload top).mp selected⟩
    · exact Or.inr ((guarded_optional_iff label source payload).mpr
        ⟨optional_payload_initial label source payload top selected, selected⟩)
  · rintro (⟨top, width⟩ | guarded)
    · exact (optional_payload_top_iff label source payload top).mpr width
    · exact (guarded_optional_iff label source payload).mp guarded |>.2

end Yulang.CommonNominalOptionalBound
