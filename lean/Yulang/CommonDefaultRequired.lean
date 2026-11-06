import Yulang.CommonDefault

/-!
# Exact whole-default inspection against a required field

The target-specific rule separates an independent optional-payload obligation
from a finite source-presence decision or an ordinary fallback/payload subtype
comparison. Source observations are taken one constructor depth after the
target payload: the initial required-field payload is bottom and imposes no
source-payload test. No whole-default comparison is an output obligation.

Presence at positive constructor depths is a Boolean computation on the
finite outer source syntax. It ignores payload references, rows, demand
environments and negative-context rank. Depth zero is a distinct cutoff and
must not be used to decide the positive-depth branch.
-/

namespace Yulang.CommonDefaultRequired

universe u v

open CommonSyntax (Layer)

/-- Outer record shape is independent of every payload reference. -/
def recordShape : Layer Row Index → Bool
  | .bottom | .emptyRecord | .exactEmpty | .record _ _ _ | .recordDefault _ _ _ => true
  | .union first last => recordShape first && recordShape last
  | .inter first last => recordShape first || recordShape last
  | .mask _ source => recordShape source
  | _ => false

/-- Required-field presence after the initial constructor cutoff. -/
def fieldPresence (hidden : List Nat) (label : Nat) : Layer Row Index → Bool
  | .bottom => true
  | .union first last => fieldPresence hidden label first && fieldPresence hidden label last
  | .inter first last => fieldPresence hidden label first || fieldPresence hidden label last
  | .mask more source => fieldPresence (hidden ++ more) label source
  | .record current _ rest =>
      if label = current ∧ current ∉ hidden then true else fieldPresence hidden label rest
  | .recordDefault current source _ =>
      if label = current ∧ current ∉ hidden then recordShape source else fieldPresence hidden label source
  | _ => false

section Finite

variable {Row : Type u} {Index : Type v}
  (leRow : Row → Row → Prop) (env : CommonFinite.Environment Row)
  (argumentOrder : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)

theorem optional_trivial_iff_records (hidden : List Nat) (source : CommonFinite.Ty Row)
    (label : Nat) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source (.optional label .trivial) ↔
      CommonFinite.MaskedProbeStep leRow env argumentOrder hidden source .records := by
  induction source generalizing hidden <;>
    simp_all [CommonFinite.MaskedProbeStep, CommonFinite.maskedProbeStep_trivial]
  all_goals split <;> simp_all [CommonFinite.maskedProbeStep_trivial]

theorem recordShape_exact (assignment : Index → CommonFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (source : Layer Row Index) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden (source.evalAt depth assignment) .records ↔
      recordShape source = true := by
  induction source generalizing hidden <;>
    simp_all [recordShape, Layer.evalAt, CommonFinite.MaskedProbeStep]
  cases depth <;> trivial

theorem fieldPresence_exact (assignment : Index → CommonFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (label : Nat) (source : Layer Row Index) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt (depth + 1) assignment) (.field label .trivial) ↔
      fieldPresence hidden label source = true := by
  induction source generalizing hidden <;>
    simp_all [fieldPresence, Layer.evalAt, CommonFinite.MaskedProbeStep,
      CommonFinite.maskedProbeStep_trivial, recordShape_exact]
  case record current head rest ih =>
    by_cases same : label = current
    · by_cases masked : current ∈ hidden <;> simp_all
    · simp_all

theorem recordShape_map (rename : Index → Target) (source : Layer Row Index) :
    recordShape (source.map rename) = recordShape source := by
  induction source <;> simp_all [Layer.map, recordShape]

theorem fieldPresence_map (rename : Index → Target) (hidden : List Nat) (label : Nat)
    (source : Layer Row Index) :
    fieldPresence hidden label (source.map rename) = fieldPresence hidden label source := by
  induction source generalizing hidden <;>
    simp_all [Layer.map, fieldPresence, recordShape_map]

end Finite

/-- The branch test is executable finite syntax inspection, not an assumed
law about the chosen producer or a solver-success condition. -/
def present (label : Nat) (source : Common.Ty) : Bool := fieldPresence [] label source

theorem present_positive_depth (label : Nat) (source : Common.Ty) (depth rank : Nat)
    (env : CommonFinite.Environment Common.Row) :
    CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy (depth + 1) source)
      (.field label .trivial) ↔ present label source = true := by
  cases rank <;> exact fieldPresence_exact Common.rowLe env _ _ depth [] label source

private theorem width_optional (leRow : Row → Row → Prop) (rank : Nat)
    (env : CommonFinite.Environment Row) (label : Nat) (obs : CommonFinite.Observation Row) :
    CommonFinite.ProbeAt leRow rank env .emptyRecord (.optional label obs) ↔ obs = .trivial := by
  cases rank <;> rfl

private theorem finite_record_below_required (leRow : Row → Row → Prop) (label : Nat)
    (payload rest : CommonFinite.Ty Row) :
    CommonFinite.ProducerLe leRow (.record label payload rest) (CommonFinite.required label payload) := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonFinite.required, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
      CommonFinite.MaskedProbeStep]
  all_goals split at * <;> simp_all

/-- Complete inspection of the selected required target in the finite
carrier. Unrelated optional-trivial observations and record roles impose no
additional constraints on a whole default. -/
theorem finite_default_required_iff (leRow : Row → Row → Prop) (label : Nat)
    (source fallback payload : CommonFinite.Ty Row) :
    CommonFinite.ProducerLe leRow (.recordDefault label source fallback)
        (CommonFinite.required label payload) ↔
      ∀ rank env obs, CommonFinite.ProbeAt leRow rank env payload obs →
        CommonFinite.ProbeAt leRow rank env source (.optional label obs) ∧
          (CommonFinite.ProbeAt leRow rank env source (.field label .trivial) ∨
            CommonFinite.ProbeAt leRow rank env fallback obs) := by
  constructor
  · intro below rank env obs accepted
    have target : CommonFinite.ProbeAt leRow rank env (CommonFinite.required label payload)
        (.field label obs) := by
      simpa only [CommonFinite.required, CommonFinite.probeAt_record_field, ↓reduceIte] using accepted
    have output := (CommonFinite.producerLe_iff_probe _ _).mp below rank env (.field label obs) target
    simpa only [CommonFinite.probeAt_default_field, ↓reduceIte] using output
  · intro selected
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    cases obs with
    | field actual inner =>
        change CommonFinite.ProbeAt leRow rank env (.record label payload .emptyRecord)
          (.field actual inner) at accepted
        rw [CommonFinite.probeAt_record_field] at accepted
        by_cases same : actual = label
        · subst actual
          simp only [↓reduceIte] at accepted
          apply (CommonFinite.probeAt_default_field rank env label label source fallback inner).mpr
          simpa only [↓reduceIte] using selected rank env inner accepted
        · simp only [same, ↓reduceIte] at accepted
          cases rank <;> exact False.elim accepted
    | optional actual inner =>
        change CommonFinite.ProbeAt leRow rank env (.record label payload .emptyRecord)
          (.optional actual inner) at accepted
        rw [CommonFinite.probeAt_record_optional] at accepted
        by_cases same : actual = label
        · subst actual
          simp only [↓reduceIte] at accepted
          apply (CommonFinite.probeAt_default_optional rank env label label source fallback inner).mpr
          exact .inl (by simpa only [↓reduceIte] using selected rank env inner accepted)
        · have trivial : inner = .trivial := by
            simpa only [same, ↓reduceIte, width_optional, or_self] using accepted
          exact (CommonFinite.probeAt_default_optional rank env label actual source fallback inner).mpr
            (.inr trivial)
    | _ => cases rank <;> exact accepted

/-- A source optional-payload requirement with the correct constructor-depth
shift. This is independently defined from atomic source and child probes. -/
def OptionalPayload (label : Nat) (source payload : Common.Ty) : Prop :=
  ∀ depth rank env obs,
    CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth payload) obs →
      CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy (depth + 1) source)
        (.optional label obs)

/-- Exact target-specific decomposition for arbitrary common types. The
ordinary child comparison appears only in the fallback branch; optional
payload information is retained in both branches. -/
theorem default_required_iff (label : Nat) (source fallback payload : Common.Ty) :
    Common.model.subTy (Common.recordDefault label source fallback) (Common.required label payload) ↔
      OptionalPayload label source payload ∧
        (present label source = true ∨ Common.model.subTy fallback payload) := by
  constructor
  · intro below
    have selected (depth : Nat) :=
      (finite_default_required_iff Common.rowLe label
        (Common.observeTy (depth + 1) source) (Common.observeTy depth fallback)
        (Common.observeTy depth payload)).mp (below (depth + 1))
    refine ⟨fun depth rank env obs accepted => (selected depth rank env obs accepted).1, ?_⟩
    by_cases available : present label source = true
    · exact .inl available
    · apply Or.inr
      intro depth
      apply (CommonFinite.producerLe_iff_probe _ _).mpr
      intro rank env obs accepted
      rcases (selected depth rank env obs accepted).2 with presence | fallback
      · exact False.elim (available ((present_positive_depth label source depth rank env).mp presence))
      · exact fallback
  · rintro ⟨optional, alternatives⟩ depth
    cases depth with
    | zero => exact finite_record_below_required Common.rowLe label .bottom (Common.observeTy 0 source)
    | succ depth =>
        apply (finite_default_required_iff Common.rowLe label
          (Common.observeTy (depth + 1) source) (Common.observeTy depth fallback)
          (Common.observeTy depth payload)).mpr
        intro rank env obs accepted
        refine ⟨optional depth rank env obs accepted, ?_⟩
        rcases alternatives with presence | fallback
        · exact .inl ((present_positive_depth label source depth rank env).mpr presence)
        · exact .inr ((CommonFinite.producerLe_iff_probe _ _).mp (fallback depth) rank env obs accepted)

/-- Solver-facing obligations for this one target constructor. The source
optional/presence information is separate from proper fallback comparison. -/
inductive Obligation where
  | optionalPayload : Nat → Common.Ty → Common.Ty → Obligation
  | sourcePresent : Nat → Common.Ty → Obligation
  | childBelow : Common.Ty → Common.Ty → Obligation

def Obligation.Holds : Obligation → Prop
  | .optionalPayload label source payload => OptionalPayload label source payload
  | .sourcePresent label source => present label source = true
  | .childBelow source target => Common.model.subTy source target

def inspectRequired (label : Nat) (source fallback payload : Common.Ty) : List (List Obligation) :=
  [[.optionalPayload label source payload, .sourcePresent label source],
    [.optionalPayload label source payload, .childBelow fallback payload]]

theorem inspect_required_exact (label : Nat) (source fallback payload : Common.Ty) :
    Common.model.subTy (Common.recordDefault label source fallback) (Common.required label payload) ↔
      ∃ branch ∈ inspectRequired label source fallback payload,
        ∀ obligation ∈ branch, obligation.Holds := by
  rw [default_required_iff]
  simp [inspectRequired, Obligation.Holds, and_or_left]

theorem optionalPayload_exactEmpty (label : Nat) (payload : Common.Ty) :
    OptionalPayload label Common.exactEmpty payload := by
  intro depth rank env obs _
  cases rank <;> simp [Common.exactEmpty, Common.observeTy, Layer.evalAt,
    CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

theorem optionalPayload_record_same (label : Nat) (head rest payload : Common.Ty) :
    OptionalPayload label (Common.record label head rest) payload ↔ Common.model.subTy head payload := by
  have observed (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
      (obs : Common.Observation) :
      CommonFinite.ProbeAt Common.rowLe rank env
          (Common.observeTy (depth + 1) (Common.record label head rest)) (.optional label obs) ↔
        CommonFinite.ProbeAt Common.rowLe rank env (Common.observeTy depth head) obs := by
    exact (CommonFinite.probeAt_record_optional rank env label label _ _ obs).trans (by
      simp only [↓reduceIte]
      rfl)
  constructor
  · intro optional depth
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    exact (observed depth rank env obs).mp (optional depth rank env obs accepted)
  · intro below depth rank env obs accepted
    exact (observed depth rank env obs).mpr
      ((CommonFinite.producerLe_iff_probe _ _).mp (below depth) rank env obs accepted)

/-- This optional producer is a union of exact absence and required presence.
Its optional-payload branch becomes exactly one child comparison. -/
def optionalSource (label : Nat) (payload : Common.Ty) : Common.Ty :=
  .union Common.exactEmpty (Common.required label payload)

theorem optionalPayload_optionalSource (label : Nat) (head payload : Common.Ty) :
    OptionalPayload label (optionalSource label head) payload ↔ Common.model.subTy head payload := by
  have absence := optionalPayload_exactEmpty label payload
  rw [← optionalPayload_record_same label head Common.emptyRecord payload]
  constructor
  · intro optional depth rank env obs accepted
    exact (CommonFinite.probeAt_union rank _ _ _).mp (optional depth rank env obs accepted) |>.2
  · intro optional depth rank env obs accepted
    apply (CommonFinite.probeAt_union rank _ _ _).mpr
    exact ⟨absence depth rank env obs accepted, optional depth rank env obs accepted⟩

theorem default_exactEmpty_required_iff (label : Nat) (fallback payload : Common.Ty) :
    Common.model.subTy (Common.recordDefault label Common.exactEmpty fallback)
        (Common.required label payload) ↔ Common.model.subTy fallback payload := by
  rw [default_required_iff]
  simp only [optionalPayload_exactEmpty label payload, true_and]
  simp [present, Common.exactEmpty, fieldPresence]

theorem default_present_required_iff (label : Nat) (head rest fallback payload : Common.Ty) :
    Common.model.subTy (Common.recordDefault label (Common.record label head rest) fallback)
        (Common.required label payload) ↔ Common.model.subTy head payload := by
  rw [default_required_iff, optionalPayload_record_same]
  simp [present, Common.record, fieldPresence]

theorem default_optional_required_iff (label : Nat) (head fallback payload : Common.Ty) :
    Common.model.subTy (Common.recordDefault label (optionalSource label head) fallback)
        (Common.required label payload) ↔
      Common.model.subTy head payload ∧ Common.model.subTy fallback payload := by
  rw [default_required_iff, optionalPayload_optionalSource]
  simp [present, optionalSource, Common.exactEmpty, Common.required, Common.record, fieldPresence]

/-- Presence is uniform at every positive depth, but the initial cutoff can
have a required bottom payload even when positive-depth presence is absent. -/
theorem presence_cutoff_differs (label rank : Nat) (fallback : Common.Ty)
    (env : CommonFinite.Environment Common.Row) :
    CommonFinite.ProbeAt Common.rowLe rank env
        (Common.observeTy 0 (Common.recordDefault label .top fallback)) (.field label .trivial) ∧
      ∀ depth, ¬ CommonFinite.ProbeAt Common.rowLe rank env
        (Common.observeTy (depth + 1) (Common.recordDefault label .top fallback)) (.field label .trivial) := by
  constructor
  · cases rank <;>
      simp [Common.recordDefault, Common.observeTy, Layer.evalAt, CommonFinite.ProbeAt,
        CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  · intro depth
    rw [present_positive_depth]
    simp [present, Common.recordDefault, fieldPresence, recordShape]

end Yulang.CommonDefaultRequired
