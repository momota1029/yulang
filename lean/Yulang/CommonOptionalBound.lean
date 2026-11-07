import Yulang.CommonTopTest
import Yulang.CommonRecordTargetProfiles
import Yulang.CommonBoundCoalescing

/-!
# Optional-payload obligations as exact common upper bounds

A guarded optional field imposes all payload observations at constructor
depth zero. A top payload, however, asks only for record shape at positive
depths. The independent finite top test selects width in that case. Otherwise
a nontrivial role witness forces the missing initial optional observation.

The resulting upper bound is exact for arbitrary common source and payload
types. Intersecting with it is an unconditional free-parameter family and
retracts every original solution in the full common demand order. This is a
single-obligation result, not a termination or completeness theorem for the
coupled symbolic solver.
-/

namespace Yulang.CommonOptionalBound

open Common (Ty Row Subtype Equivalent)
open CommonSyntax (Layer)
open CommonDefaultRequired (OptionalPayload)
open CommonRecordTailProfiles (initialOptional)
open CommonRecordTargetProfiles

universe u v

section Finite

variable {R : Type u} {leRow : R → R → Prop}

theorem finite_optional_iff (source payload : CommonFinite.Ty R) (label : Nat) :
    CommonFinite.ProducerLe leRow source (.union .exactEmpty (CommonFinite.required label payload)) ↔
      ∀ rank env obs, CommonFinite.ProbeAt leRow rank env payload obs →
        CommonFinite.ProbeAt leRow rank env source (.optional label obs) := by
  constructor
  · intro below rank env obs accepted
    apply (CommonFinite.producerLe_iff_probe _ _).mp below rank env (.optional label obs)
    rw [CommonFinite.probeAt_union]
    constructor
    · cases rank <;> exact Or.inl (by simp)
    · simpa only [CommonFinite.required, CommonFinite.probeAt_record_optional, ↓reduceIte] using accepted
  · intro selected
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have recorded : CommonFinite.ProbeAt leRow rank env source .records := by
      have trivial := selected rank env .trivial (CommonFinite.probeAt_trivial rank payload)
      cases rank <;> exact (CommonDefaultRequired.optional_trivial_iff_records
        leRow env _ [] source label).mp trivial
    have both := (CommonFinite.probeAt_union rank _ _ obs).mp accepted
    cases obs with
    | trivial => exact CommonFinite.probeAt_trivial rank source
    | records => exact recorded
    | role name => cases rank <;> exact records_implies_role source [] name both.1 recorded
    | optional current inner =>
        have required := both.2
        by_cases same : current = label
        · subst current
          apply selected rank env inner
          simpa only [CommonFinite.required, CommonFinite.probeAt_record_optional, ↓reduceIte] using required
        · simp only [CommonFinite.required, CommonFinite.probeAt_record_optional, same, ↓reduceIte] at required
          have trivial : inner = .trivial := by
            cases rank <;> exact required.elim id id
          subst inner
          cases rank <;> exact (CommonDefaultRequired.optional_trivial_iff_records
            leRow env _ [] source current).mpr recorded
    | _ => cases rank <;> exact False.elim both.1

end Finite

/-- Any nontrivial positive-depth optional observation already forces the
initial Boolean observation. The converse is intentionally not asserted. -/
theorem optional_positive_initial {R : Type u} {Index : Type v}
    (leRow : R → R → Prop) (env : CommonFinite.Environment R)
    (argumentOrder : CommonFinite.Ty R → CommonFinite.Ty R → Prop)
    (assignment : Index → CommonFinite.Ty R) (depth : Nat)
    (hidden : List Nat) (label : Nat) (source : Layer R Index)
    (obs : CommonFinite.Observation R) (notTrivial : obs ≠ .trivial)
    (accepted : CommonFinite.MaskedProbeStep leRow env argumentOrder hidden
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
      · simp only [Layer.evalAt, CommonFinite.MaskedProbeStep, active, ↓reduceIte] at accepted
        simpa only [initialOptional, active, ↓reduceIte] using
          ih hidden (accepted.resolve_right notTrivial)
  | recordDefault current source fallback ih =>
      by_cases active : label = current ∧ current ∉ hidden
      · simp [initialOptional, active]
      · simp only [Layer.evalAt, CommonFinite.MaskedProbeStep, active, ↓reduceIte] at accepted
        simpa only [initialOptional, active, ↓reduceIte] using
          ih hidden (accepted.resolve_right notTrivial)
  | exactEmpty =>
      simpa only [initialOptional, decide_eq_true_eq] using accepted.resolve_right notTrivial
  | emptyRecord => exact False.elim (notTrivial accepted)
  | _ => exact False.elim accepted

theorem optional_payload_shape (label : Nat) (source payload : Ty)
    (selected : OptionalPayload label source payload) :
    CommonDefaultRequired.recordShape source = true := by
  let env : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have trivial := selected 0 0 env .trivial (CommonFinite.probeAt_trivial 0 _)
  have shaped := (CommonDefaultRequired.optional_trivial_iff_records
    Common.rowLe env _ [] (Common.observeTy 1 source) label).mp trivial
  exact (record_shape_probe source 1 0 env).mp shaped

theorem optional_payload_initial (label : Nat) (source payload : Ty)
    (positive : CommonTopTest.nontrivial payload = true)
    (selected : OptionalPayload label source payload) :
    initialOptional [] label source = true := by
  have accepted := selected 0 0 (CommonTopTest.roleEnvironment payload) (.role 0)
    (CommonTopTest.role_witness payload positive 0 0)
  exact optional_positive_initial Common.rowLe (CommonTopTest.roleEnvironment payload) _ _
    0 [] label source (.role 0) (by intro impossible; cases impossible) accepted

def guardedOptional (label : Nat) (payload : Ty) : Ty :=
  .union Common.exactEmpty (Common.required label payload)

theorem guarded_optional_iff (label : Nat) (source payload : Ty) :
    Subtype source (guardedOptional label payload) ↔
      initialOptional [] label source = true ∧ OptionalPayload label source payload := by
  constructor
  · intro below
    constructor
    · let env : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
      have accepted := (finite_optional_iff (Common.observeTy 0 source) .bottom label).mp
        (below 0) 0 env .impossible (by trivial)
      exact (CommonRecordTailProfiles.initial_optional_exact [] label source 0 env
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
          cases rank <;> exact (CommonDefaultRequired.optional_trivial_iff_records
            Common.rowLe env _ [] (Common.observeTy 0 source) label).mpr recorded
        · simpa only [CommonFinite.maskedProbeAt_nil] using
            (CommonRecordTailProfiles.initial_optional_exact [] label source rank env obs trivial).mpr initial
    | succ depth => exact selected depth rank env obs accepted

theorem optional_payload_top_iff (label : Nat) (source payload : Ty)
    (empty : CommonTopTest.nontrivial payload = false) :
    OptionalPayload label source payload ↔ Subtype source Common.emptyRecord := by
  constructor
  · intro selected
    exact (subtype_emptyRecord_iff source).mpr (optional_payload_shape label source payload selected)
  · intro width depth rank env obs accepted
    have same := (CommonTopTest.top_iff payload).mpr empty
    have top := (CommonFinite.producerLe_iff_probe _ _).mp (same.2 depth) rank env obs accepted
    have trivial : obs = .trivial := by
      cases obs <;> cases rank <;> simp_all [Common.observeTy, Layer.evalAt,
        CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
    subst obs
    apply (CommonFinite.producerLe_iff_probe _ _).mp (width (depth + 1)) rank env (.optional label .trivial)
    cases rank <;> rfl

/-- The branch is an independent finite syntax test, not a residual predicate
on the free payload parameter. -/
def bound (label : Nat) (payload : Ty) : Ty :=
  if CommonTopTest.nontrivial payload then guardedOptional label payload else Common.emptyRecord

theorem optional_payload_bound_exact (label : Nat) (source payload : Ty) :
    OptionalPayload label source payload ↔ Subtype source (bound label payload) := by
  cases found : CommonTopTest.nontrivial payload with
  | false =>
      simpa only [bound, found, Bool.false_eq_true, ↓reduceIte] using
        optional_payload_top_iff label source payload found
  | true =>
      simp only [bound, found, ↓reduceIte, guarded_optional_iff]
      exact ⟨fun selected => ⟨optional_payload_initial label source payload found selected, selected⟩,
        fun selected => selected.2⟩

/-- An inference-time finite split containing only ordinary subtype tests.
The top case needs no negative Boolean guard; the guarded branch is sound
also when the payload happens to be top. -/
theorem optional_payload_branches_exact (label : Nat) (source payload : Ty) :
    OptionalPayload label source payload ↔
      (Subtype .top payload ∧ Subtype source Common.emptyRecord) ∨
        Subtype source (guardedOptional label payload) := by
  constructor
  · intro selected
    cases found : CommonTopTest.nontrivial payload with
    | false =>
        exact Or.inl ⟨((CommonTopTest.top_iff payload).mpr found).2,
          (optional_payload_top_iff label source payload found).mp selected⟩
    | true =>
        exact Or.inr ((guarded_optional_iff label source payload).mpr
          ⟨optional_payload_initial label source payload found selected, selected⟩)
  · rintro (⟨topBelow, width⟩ | guarded)
    · have empty := (CommonTopTest.top_iff payload).mp
        ⟨CommonBoundCoalescing.le_top payload, topBelow⟩
      exact (optional_payload_top_iff label source payload empty).mpr width
    · exact (guarded_optional_iff label source payload).mp guarded |>.2

theorem bound_mono (label : Nat) {first last : Ty} (below : Subtype first last) :
    Subtype (bound label first) (bound label last) := by
  apply (optional_payload_bound_exact label _ last).mp
  have own := (optional_payload_bound_exact label (bound label first) first).mpr
    (Common.subtype_refl _)
  intro depth rank env obs accepted
  exact own depth rank env obs
    ((CommonFinite.producerLe_iff_probe _ _).mp (below depth) rank env obs accepted)

def MaskedOptionalPayload (hidden : List Nat) (label : Nat) (source payload : Ty) : Prop :=
  ∀ depth rank env obs,
    CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth payload) obs →
      CommonFinite.MaskedProbeAt Common.rowLe rank env hidden
        (Common.observeTy (depth + 1) source) (.optional label obs)

theorem masked_optional_as_optional (hidden : List Nat) (label : Nat) (source payload : Ty) :
    MaskedOptionalPayload hidden label source payload ↔
      OptionalPayload label (Common.mask hidden source) payload := by
  simp only [MaskedOptionalPayload, OptionalPayload, Common.observeTy, Common.mask,
    Layer.evalAt, CommonFinite.probeAt_mask]

/-- All masks are admitted. This is a bound on the masked source; it does not
claim a retraction of the original unmasked source from an independently
chosen masked type. -/
theorem masked_optional_bound_exact (hidden : List Nat) (label : Nat) (source payload : Ty) :
    MaskedOptionalPayload hidden label source payload ↔
      Subtype (Common.mask hidden source) (bound label payload) := by
  rw [masked_optional_as_optional, optional_payload_bound_exact]

def narrow (label : Nat) (payload parameter : Ty) : Ty :=
  .inter parameter (bound label payload)

theorem narrow_mono (label : Nat) {payload payload' parameter parameter' : Ty}
    (payloadBelow : Subtype payload payload') (parameterBelow : Subtype parameter parameter') :
    Subtype (narrow label payload parameter) (narrow label payload' parameter') :=
  Common.common_inter_mono parameterBelow (bound_mono label payloadBelow)

/-- Every unconstrained common parameter gives a solution. -/
theorem narrow_satisfies (label : Nat) (payload parameter : Ty) :
    OptionalPayload label (narrow label payload parameter) payload :=
  (optional_payload_bound_exact label _ payload).mpr
    (CommonBoundCoalescing.inter_le_right parameter (bound label payload))

/-- Retraction preserves the entire type, including unrelated fields, roles,
negative children, regular states, and the initial constructor cutoff. -/
theorem narrow_retract (label : Nat) (source payload : Ty)
    (selected : OptionalPayload label source payload) :
    Equivalent (narrow label payload source) source :=
  ⟨CommonBoundCoalescing.inter_le_left source (bound label payload),
    (Common.common_inter_is_meet source (bound label payload) source).mpr
      ⟨Common.subtype_refl source, (optional_payload_bound_exact label source payload).mp selected⟩⟩

theorem narrow_instances_exact (label : Nat) (source payload : Ty) :
    OptionalPayload label source payload ↔
      ∃ parameter : Ty, Equivalent (narrow label payload parameter) source := by
  constructor
  · intro selected
    exact ⟨source, narrow_retract label source payload selected⟩
  · rintro ⟨parameter, same⟩
    apply (optional_payload_bound_exact label source payload).mpr
    exact Common.subtype_trans same.2
      ((optional_payload_bound_exact label _ payload).mp (narrow_satisfies label payload parameter))

/-- The top branch must not add the guarded optional type's depth-zero test. -/
theorem width_optional_top (label : Nat) : OptionalPayload label Common.emptyRecord .top :=
  (optional_payload_top_iff label Common.emptyRecord .top rfl).mpr (Common.subtype_refl _)

theorem width_not_below_guarded_top (label : Nat) :
    ¬ Subtype Common.emptyRecord (guardedOptional label .top) := by
  intro below
  have impossible := (guarded_optional_iff label Common.emptyRecord .top).mp below |>.1
  cases impossible

end Yulang.CommonOptionalBound
