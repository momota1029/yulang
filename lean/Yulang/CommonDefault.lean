import Yulang.Common
import Yulang.CommonFinitePresence

/-!
# Whole-record default laws for the regular common carrier

Default insertion observes its result field at the same payload depth as an
ordinary record constructor. At depth zero the field payload is bottom; at
successor depths the concrete finite default interpretation reads the source
and the fallback. This prevents an unknown width field from being subjected
to a payload demand before a payload reference has been unfolded.

These are producer-demand laws on arbitrary regular common syntax. Strict
fallback evaluation remains expressed by the separate runtime data readout.
-/

namespace Yulang.Common

private theorem finite_record_below_required (label : Nat)
    (payload rest : CommonFinite.Ty Row) :
    CommonFinite.ProducerLe rowLe (.record label payload rest) (CommonFinite.required label payload) := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonFinite.required, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
      CommonFinite.MaskedProbeStep]
  all_goals split at * <;> simp_all

private theorem finite_record_below_width (label : Nat)
    (payload rest : CommonFinite.Ty Row) :
    CommonFinite.ProducerLe rowLe (.record label payload rest) .emptyRecord := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  all_goals split <;> simp_all

private theorem finite_top_probe (rank : Nat) (env : CommonFinite.Environment Row)
    (obs : CommonFinite.Observation Row) :
    CommonFinite.ProbeAt rowLe rank env .top obs ↔ obs = .trivial := by
  cases rank <;> cases obs <;>
    simp [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

private theorem finite_width_optional (rank : Nat) (env : CommonFinite.Environment Row)
    (label : Nat) (obs : CommonFinite.Observation Row) :
    CommonFinite.ProbeAt rowLe rank env .emptyRecord (.optional label obs) ↔ obs = .trivial := by
  cases rank <;> rfl

private theorem finite_default_guarantees_field (label : Nat)
    (source fallback : CommonFinite.Ty Row)
    (sourceRecord : CommonFinite.ProducerLe rowLe source .emptyRecord) :
    CommonFinite.ProducerLe rowLe (.recordDefault label source fallback)
      (CommonFinite.required label .top) := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  have sourceOptional : CommonFinite.ProbeAt rowLe rank env source (.optional label .trivial) :=
    (CommonFinite.producerLe_iff_probe _ _).mp sourceRecord rank env (.optional label .trivial)
      ((finite_width_optional rank env label .trivial).mpr rfl)
  cases obs with
  | field actual payload =>
      change CommonFinite.ProbeAt rowLe rank env (.record label .top .emptyRecord)
        (.field actual payload) at accepted
      rw [CommonFinite.probeAt_record_field] at accepted
      by_cases same : actual = label
      · subst actual
        simp only [↓reduceIte, finite_top_probe] at accepted
        subst payload
        apply (CommonFinite.probeAt_default_field rank env label label source fallback .trivial).mpr
        simp only [↓reduceIte]
        exact ⟨sourceOptional, .inr (CommonFinite.probeAt_trivial rank fallback)⟩
      · simp only [same, ↓reduceIte] at accepted
        cases rank <;> exact False.elim accepted
  | optional actual payload =>
      change CommonFinite.ProbeAt rowLe rank env (.record label .top .emptyRecord)
        (.optional actual payload) at accepted
      rw [CommonFinite.probeAt_record_optional] at accepted
      have trivial : payload = .trivial := by
        by_cases same : actual = label <;>
          simpa only [same, ↓reduceIte, finite_top_probe, finite_width_optional, or_self] using accepted
      subst payload
      exact (CommonFinite.probeAt_default_optional rank env label actual source fallback .trivial).mpr (.inr rfl)
  | _ => cases rank <;> exact accepted

private theorem finite_shadowed_head (label : Nat)
    (payload hidden rest : CommonFinite.Ty Row) :
    CommonFinite.ProducerEq rowLe (.record label payload (.record label hidden rest))
      (.record label payload rest) := by
  apply (CommonFinite.producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;>
    simp [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  all_goals split <;> simp_all

/-- Every whole default has record shape at every constructor approximation,
including when its source syntax is not itself a well-typed record producer. -/
theorem common_default_below_width (label : Nat) (source fallback : Ty) :
    model.subTy (recordDefault label source fallback) emptyRecord := by
  intro depth
  cases depth with
  | zero => exact finite_record_below_width label .bottom (observeTy 0 source)
  | succ depth =>
      exact CommonFinite.recordDefault_below_width label
        (observeTy (depth + 1) source) (observeTy depth fallback)

/-- For every source below width-record and every fallback type, the selected
field is required after insertion. No solver success, regularity certificate,
inhabitation premise, or bound on payload syntax is required. -/
theorem default_guarantees_field (label : Nat) (source fallback : Ty)
    (sourceRecord : model.subTy source emptyRecord) :
    model.subTy (recordDefault label source fallback) (required label .top) := by
  intro depth
  cases depth with
  | zero => exact finite_record_below_required label .bottom (observeTy 0 source)
  | succ depth =>
      exact finite_default_guarantees_field label
        (observeTy (depth + 1) source) (observeTy depth fallback) (sourceRecord (depth + 1))

/-- Inserting into the width record guarantees the selected field even when
the first payload approximation of the fallback is bottom. -/
theorem default_width_guarantees_field (label : Nat) (fallback : Ty) :
    model.subTy (recordDefault label emptyRecord fallback) (required label .top) :=
  default_guarantees_field label emptyRecord fallback (subtype_refl emptyRecord)

/-- Known absence gives an ordinary record with the whole fallback payload,
while preserving exact absence of unrelated fields. -/
theorem default_exactEmpty (label : Nat) (fallback : Ty) :
    Equivalent (recordDefault label exactEmpty fallback) (record label fallback exactEmpty) := by
  have observed (depth : Nat) : CommonFinite.ProducerEq rowLe
      (observeTy depth (recordDefault label exactEmpty fallback))
      (observeTy depth (record label fallback exactEmpty)) := by
    cases depth with
    | zero => exact CommonFinite.producerEq_refl _
    | succ depth => exact CommonFinite.default_exactEmpty label (observeTy depth fallback)
  exact ⟨fun depth => (observed depth).1, fun depth => (observed depth).2⟩

/-- Known presence preserves the entire original producer record. The source
payload and tail may contain arbitrary masks and recursive graphs. -/
theorem default_present_record (label : Nat) (payload rest fallback : Ty) :
    Equivalent (recordDefault label (record label payload rest) fallback) (record label payload rest) := by
  have observed (depth : Nat) : CommonFinite.ProducerEq rowLe
      (observeTy depth (recordDefault label (record label payload rest) fallback))
      (observeTy depth (record label payload rest)) := by
    cases depth with
    | zero => exact finite_shadowed_head label .bottom .bottom (observeTy 0 rest)
    | succ depth =>
        exact CommonFinite.default_present_record label
          (observeTy depth payload) (observeTy (depth + 1) rest) (observeTy depth fallback)
  exact ⟨fun depth => (observed depth).1, fun depth => (observed depth).2⟩

/-- Whole default is monotone in both source and fallback for every common
regular type. Its initial payload cutoff is the same on both sides. -/
theorem common_default_mono (label : Nat) {source source' fallback fallback' : Ty}
    (base : model.subTy source source') (default : model.subTy fallback fallback') :
    model.subTy (recordDefault label source fallback) (recordDefault label source' fallback') := by
  intro depth
  cases depth with
  | zero => exact CommonFinite.producerLe_record_mono label (CommonFinite.producerLe_refl .bottom) (base 0)
  | succ depth => exact CommonFinite.producerLe_recordDefault label (base (depth + 1)) (default depth)

theorem common_default_congr (label : Nat) {source source' fallback fallback' : Ty}
    (base : Equivalent source source') (default : Equivalent fallback fallback') :
    Equivalent (recordDefault label source fallback) (recordDefault label source' fallback') :=
  ⟨common_default_mono label base.1 default.1, common_default_mono label base.2 default.2⟩

/-- An unrelated field demand is passed to the whole source at exactly the
same constructor depth and with the same arbitrary demand environment. -/
theorem default_preserves_other_field (current label : Nat) (different : label ≠ current)
    (source fallback : Ty) (depth rank : Nat) (env : Environment) (payload : Observation) :
    AcceptAt depth rank env (recordDefault current source fallback) (.atom (.field label payload)) ↔
      AcceptAt depth rank env source (.atom (.field label payload)) := by
  cases depth <;> cases rank <;>
    simp [AcceptAt, recordDefault, observeTy, CommonSyntax.Layer.evalAt,
      CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep,
      CommonFinite.AcceptAt, CommonFinite.Demand.tests, different]

end Yulang.Common
