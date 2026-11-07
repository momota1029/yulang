import Yulang.CommonNominalDefault
import Yulang.CommonNominalTailElimination

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

namespace Yulang.CommonNominalDefaultRequired

universe u v

open CommonNominalSyntax (Layer)

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
  (leRow : Row → Row → Prop) (env : CommonNominalFinite.Environment Row)
  (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)

theorem optional_trivial_iff_records (hidden : List Nat) (source : CommonNominalFinite.Ty Row)
    (label : Nat) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden source (.optional label .trivial) ↔
      CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden source .records := by
  induction source using CommonNominalFinite.Ty.rec
      (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing hidden <;>
    simp_all [CommonNominalFinite.MaskedProbeStep, CommonNominalFinite.maskedProbeStep_trivial]
  all_goals split <;> simp_all [CommonNominalFinite.maskedProbeStep_trivial]

theorem recordShape_exact (assignment : Index → CommonNominalFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (source : Layer Row Index) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden (source.evalAt depth assignment) .records ↔
      recordShape source = true := by
  induction source generalizing hidden <;>
    simp_all [recordShape, Layer.evalAt, CommonNominalFinite.MaskedProbeStep]
  cases depth <;> trivial

theorem fieldPresence_exact (assignment : Index → CommonNominalFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (label : Nat) (source : Layer Row Index) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt (depth + 1) assignment) (.field label .trivial) ↔
      fieldPresence hidden label source = true := by
  induction source generalizing hidden <;>
    simp_all [fieldPresence, Layer.evalAt, CommonNominalFinite.MaskedProbeStep,
      CommonNominalFinite.maskedProbeStep_trivial, recordShape_exact]
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
def present (label : Nat) (source : CommonNominalCarrier.Ty) : Bool := fieldPresence [] label source

theorem present_positive_depth (label : Nat) (source : CommonNominalCarrier.Ty) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy (depth + 1) source)
      (.field label .trivial) ↔ present label source = true := by
  cases rank <;> exact fieldPresence_exact Common.rowLe env _ _ depth [] label source

private theorem width_optional (leRow : Row → Row → Prop) (rank : Nat)
    (env : CommonNominalFinite.Environment Row) (label : Nat) (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.ProbeAt leRow rank env .emptyRecord (.optional label obs) ↔ obs = .trivial := by
  cases rank <;> rfl

private theorem finite_record_below_required (leRow : Row → Row → Prop) (label : Nat)
    (payload rest : CommonNominalFinite.Ty Row) :
    CommonNominalFinite.ProducerLe leRow (.record label payload rest) (CommonNominalFinite.required label payload) := by
  apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonNominalFinite.required, CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
      CommonNominalFinite.MaskedProbeStep]
  all_goals split at * <;> simp_all

/-- Complete inspection of the selected required target in the finite
carrier. Unrelated optional-trivial observations and record roles impose no
additional constraints on a whole default. -/
theorem finite_default_required_iff (leRow : Row → Row → Prop) (label : Nat)
    (source fallback payload : CommonNominalFinite.Ty Row) :
    CommonNominalFinite.ProducerLe leRow (.recordDefault label source fallback)
        (CommonNominalFinite.required label payload) ↔
      ∀ rank env obs, CommonNominalFinite.ProbeAt leRow rank env payload obs →
        CommonNominalFinite.ProbeAt leRow rank env source (.optional label obs) ∧
          (CommonNominalFinite.ProbeAt leRow rank env source (.field label .trivial) ∨
            CommonNominalFinite.ProbeAt leRow rank env fallback obs) := by
  constructor
  · intro below rank env obs accepted
    have target : CommonNominalFinite.ProbeAt leRow rank env (CommonNominalFinite.required label payload)
        (.field label obs) := by
      simpa only [CommonNominalFinite.required, CommonNominalFinite.probeAt_record_field, ↓reduceIte] using accepted
    have output := (CommonNominalFinite.producerLe_iff_probe _ _).mp below rank env (.field label obs) target
    simpa only [CommonNominalFinite.probeAt_default_field, ↓reduceIte] using output
  · intro selected
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    cases obs with
    | field actual inner =>
        change CommonNominalFinite.ProbeAt leRow rank env (.record label payload .emptyRecord)
          (.field actual inner) at accepted
        rw [CommonNominalFinite.probeAt_record_field] at accepted
        by_cases same : actual = label
        · subst actual
          simp only [↓reduceIte] at accepted
          apply (CommonNominalFinite.probeAt_default_field rank env label label source fallback inner).mpr
          simpa only [↓reduceIte] using selected rank env inner accepted
        · simp only [same, ↓reduceIte] at accepted
          cases rank <;> exact False.elim accepted
    | optional actual inner =>
        change CommonNominalFinite.ProbeAt leRow rank env (.record label payload .emptyRecord)
          (.optional actual inner) at accepted
        rw [CommonNominalFinite.probeAt_record_optional] at accepted
        by_cases same : actual = label
        · subst actual
          simp only [↓reduceIte] at accepted
          apply (CommonNominalFinite.probeAt_default_optional rank env label label source fallback inner).mpr
          exact .inl (by simpa only [↓reduceIte] using selected rank env inner accepted)
        · have trivial : inner = .trivial := by
            simpa only [same, ↓reduceIte, width_optional, or_self] using accepted
          exact (CommonNominalFinite.probeAt_default_optional rank env label actual source fallback inner).mpr
            (.inr trivial)
    | _ => cases rank <;> exact accepted

/-- A source optional-payload requirement with the correct constructor-depth
shift. This is independently defined from atomic source and child probes. -/
def OptionalPayload (label : Nat) (source payload : CommonNominalCarrier.Ty) : Prop :=
  ∀ depth rank env obs,
    CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth payload) obs →
      CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy (depth + 1) source)
        (.optional label obs)

/-- Exact target-specific decomposition for arbitrary common types. The
ordinary child comparison appears only in the fallback branch; optional
payload information is retained in both branches. -/
theorem default_required_iff (label : Nat) (source fallback payload : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.required label payload) ↔
      OptionalPayload label source payload ∧
        (present label source = true ∨ CommonNominalCarrier.model.subTy fallback payload) := by
  constructor
  · intro below
    have selected (depth : Nat) :=
      (finite_default_required_iff Common.rowLe label
        (CommonNominalCarrier.observeTy (depth + 1) source) (CommonNominalCarrier.observeTy depth fallback)
        (CommonNominalCarrier.observeTy depth payload)).mp (below (depth + 1))
    refine ⟨fun depth rank env obs accepted => (selected depth rank env obs accepted).1, ?_⟩
    by_cases available : present label source = true
    · exact .inl available
    · apply Or.inr
      intro depth
      apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
      intro rank env obs accepted
      rcases (selected depth rank env obs accepted).2 with presence | fallback
      · exact False.elim (available ((present_positive_depth label source depth rank env).mp presence))
      · exact fallback
  · rintro ⟨optional, alternatives⟩ depth
    cases depth with
    | zero => exact finite_record_below_required Common.rowLe label .bottom (CommonNominalCarrier.observeTy 0 source)
    | succ depth =>
        apply (finite_default_required_iff Common.rowLe label
          (CommonNominalCarrier.observeTy (depth + 1) source) (CommonNominalCarrier.observeTy depth fallback)
          (CommonNominalCarrier.observeTy depth payload)).mpr
        intro rank env obs accepted
        refine ⟨optional depth rank env obs accepted, ?_⟩
        rcases alternatives with presence | fallback
        · exact .inl ((present_positive_depth label source depth rank env).mpr presence)
        · exact .inr ((CommonNominalFinite.producerLe_iff_probe _ _).mp (fallback depth) rank env obs accepted)

/-- Solver-facing obligations for this one target constructor. The source
optional/presence information is separate from proper fallback comparison. -/
inductive Obligation where
  | optionalPayload : Nat → CommonNominalCarrier.Ty → CommonNominalCarrier.Ty → Obligation
  | sourcePresent : Nat → CommonNominalCarrier.Ty → Obligation
  | childBelow : CommonNominalCarrier.Ty → CommonNominalCarrier.Ty → Obligation

def Obligation.Holds : Obligation → Prop
  | .optionalPayload label source payload => OptionalPayload label source payload
  | .sourcePresent label source => present label source = true
  | .childBelow source target => CommonNominalCarrier.model.subTy source target

def inspectRequired (label : Nat) (source fallback payload : CommonNominalCarrier.Ty) : List (List Obligation) :=
  [[.optionalPayload label source payload, .sourcePresent label source],
    [.optionalPayload label source payload, .childBelow fallback payload]]

theorem inspect_required_exact (label : Nat) (source fallback payload : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.required label payload) ↔
      ∃ branch ∈ inspectRequired label source fallback payload,
        ∀ obligation ∈ branch, obligation.Holds := by
  rw [default_required_iff]
  simp [inspectRequired, Obligation.Holds, and_or_left]

theorem optionalPayload_exactEmpty (label : Nat) (payload : CommonNominalCarrier.Ty) :
    OptionalPayload label CommonNominalCarrier.exactEmpty payload := by
  intro depth rank env obs _
  cases rank <;> simp [CommonNominalCarrier.exactEmpty, CommonNominalCarrier.observeTy, Layer.evalAt,
    CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep]

theorem optionalPayload_record_same (label : Nat) (head rest payload : CommonNominalCarrier.Ty) :
    OptionalPayload label (CommonNominalCarrier.record label head rest) payload ↔ CommonNominalCarrier.model.subTy head payload := by
  have observed (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
      (obs : CommonNominalCarrier.Observation) :
      CommonNominalFinite.ProbeAt Common.rowLe rank env
          (CommonNominalCarrier.observeTy (depth + 1) (CommonNominalCarrier.record label head rest)) (.optional label obs) ↔
        CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth head) obs := by
    exact (CommonNominalFinite.probeAt_record_optional rank env label label _ _ obs).trans (by
      simp only [↓reduceIte]
      rfl)
  constructor
  · intro optional depth
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    exact (observed depth rank env obs).mp (optional depth rank env obs accepted)
  · intro below depth rank env obs accepted
    exact (observed depth rank env obs).mpr
      ((CommonNominalFinite.producerLe_iff_probe _ _).mp (below depth) rank env obs accepted)

/-- This optional producer is a union of exact absence and required presence.
Its optional-payload branch becomes exactly one child comparison. -/
def optionalSource (label : Nat) (payload : CommonNominalCarrier.Ty) : CommonNominalCarrier.Ty :=
  .union CommonNominalCarrier.exactEmpty (CommonNominalCarrier.required label payload)

theorem optionalPayload_optionalSource (label : Nat) (head payload : CommonNominalCarrier.Ty) :
    OptionalPayload label (optionalSource label head) payload ↔ CommonNominalCarrier.model.subTy head payload := by
  have absence := optionalPayload_exactEmpty label payload
  rw [← optionalPayload_record_same label head CommonNominalCarrier.emptyRecord payload]
  constructor
  · intro optional depth rank env obs accepted
    exact (CommonNominalFinite.probeAt_union rank _ _ _).mp (optional depth rank env obs accepted) |>.2
  · intro optional depth rank env obs accepted
    apply (CommonNominalFinite.probeAt_union rank _ _ _).mpr
    exact ⟨absence depth rank env obs accepted, optional depth rank env obs accepted⟩

theorem default_exactEmpty_required_iff (label : Nat) (fallback payload : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label CommonNominalCarrier.exactEmpty fallback)
        (CommonNominalCarrier.required label payload) ↔ CommonNominalCarrier.model.subTy fallback payload := by
  rw [default_required_iff]
  simp only [optionalPayload_exactEmpty label payload, true_and]
  simp [present, CommonNominalCarrier.exactEmpty, fieldPresence]

theorem default_present_required_iff (label : Nat) (head rest fallback payload : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label (CommonNominalCarrier.record label head rest) fallback)
        (CommonNominalCarrier.required label payload) ↔ CommonNominalCarrier.model.subTy head payload := by
  rw [default_required_iff, optionalPayload_record_same]
  simp [present, CommonNominalCarrier.record, fieldPresence]

theorem default_optional_required_iff (label : Nat) (head fallback payload : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.model.subTy (CommonNominalCarrier.recordDefault label (optionalSource label head) fallback)
        (CommonNominalCarrier.required label payload) ↔
      CommonNominalCarrier.model.subTy head payload ∧ CommonNominalCarrier.model.subTy fallback payload := by
  rw [default_required_iff, optionalPayload_optionalSource]
  simp [present, optionalSource, CommonNominalCarrier.exactEmpty, CommonNominalCarrier.required, CommonNominalCarrier.record, fieldPresence]

/-- Presence is uniform at every positive depth, but the initial cutoff can
have a required bottom payload even when positive-depth presence is absent. -/
theorem presence_cutoff_differs (label rank : Nat) (fallback : CommonNominalCarrier.Ty)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env
        (CommonNominalCarrier.observeTy 0 (CommonNominalCarrier.recordDefault label .top fallback)) (.field label .trivial) ∧
      ∀ depth, ¬ CommonNominalFinite.ProbeAt Common.rowLe rank env
        (CommonNominalCarrier.observeTy (depth + 1) (CommonNominalCarrier.recordDefault label .top fallback)) (.field label .trivial) := by
  constructor
  · cases rank <;>
      simp [CommonNominalCarrier.recordDefault, CommonNominalCarrier.observeTy, Layer.evalAt, CommonNominalFinite.ProbeAt,
        CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep]
  · intro depth
    rw [present_positive_depth]
    simp [present, CommonNominalCarrier.recordDefault, fieldPresence, recordShape]

end Yulang.CommonNominalDefaultRequired
