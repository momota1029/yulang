import Yulang.CommonNominalFiniteConstructors

/-!
# Outer mask laws for the finite common carrier

All payloads and arbitrary negative argument assignments are retained.
The laws follow from recursive interpretation and hidden-label membership;
no solver property or postulated mask equation occurs in the definitions.
-/

namespace Yulang.CommonNominalFinite

universe u
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}
  {argumentOrder : Ty Row → Ty Row → Prop}

@[simp] theorem maskedProbeStep_trivial (hidden : List Nat) (type : Ty Row) :
    MaskedProbeStep leRow env argumentOrder hidden type .trivial := by
  cases type <;> trivial

@[simp] theorem maskedProbeStep_or_trivial (hidden : List Nat)
    (type : Ty Row) (obs : Observation Row) :
    (MaskedProbeStep leRow env argumentOrder hidden type obs ∨ obs = .trivial) ↔
      MaskedProbeStep leRow env argumentOrder hidden type obs := by
  constructor
  · rintro (valid | same)
    · exact valid
    · cases same
      exact maskedProbeStep_trivial hidden type
  · exact Or.inl

/-- A trivial optional payload asks exactly for record shape, even through
unions, intersections and nested outer masks. -/
@[simp] theorem maskedProbeStep_optional_trivial (hidden : List Nat)
    (type : Ty Row) (label : Nat) :
    MaskedProbeStep leRow env argumentOrder hidden type (.optional label .trivial) ↔
      MaskedProbeStep leRow env argumentOrder hidden type .records := by
  induction type using Ty.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing hidden with
  | union a b iha ihb | inter a b iha ihb => simp [MaskedProbeStep, iha, ihb]
  | mask more type ih => simpa [MaskedProbeStep] using ih (hidden ++ more)
  | record current payload rest ihp ihr => simp [MaskedProbeStep, maskedProbeStep_trivial]
  | recordDefault current source fallback ihs ihf => simp [MaskedProbeStep]
  | _ => simp [MaskedProbeStep]

@[simp] theorem maskedProbeStep_mask (hidden more : List Nat) (type : Ty Row)
    (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder hidden (.mask more type) obs ↔
      MaskedProbeStep leRow env argumentOrder (hidden ++ more) type obs := by
  cases obs <;> simp [MaskedProbeStep]

/-- Order, repetition and labels outside the current type cannot affect
interpretation when they describe the same hidden-label set. -/
theorem maskedProbeStep_congr (first last : List Nat)
    (same : ∀ label, label ∈ first ↔ label ∈ last)
    (type : Ty Row) (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder first type obs ↔
      MaskedProbeStep leRow env argumentOrder last type obs := by
  induction type using Ty.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing first last obs with
  | base | float | nominal | bottom | top | pair | emptyRecord | exactEmpty | variant | arrow =>
      cases obs <;> simp [MaskedProbeStep, same]
  | union a b iha ihb | inter a b iha ihb =>
      cases obs <;> simp [MaskedProbeStep, iha first last same, ihb first last same]
  | record label payload rest ihp ihr =>
      cases obs <;> simp [MaskedProbeStep, same, ihr first last same]
  | recordDefault label source fallback ihs ihf =>
      cases obs <;> simp [MaskedProbeStep, same, ihs first last same]
  | nil | cons | inl | inr => trivial
  | mask hidden type ih =>
      rw [maskedProbeStep_mask, maskedProbeStep_mask]
      apply ih
      intro label
      simp only [List.mem_append, same]

@[simp] theorem maskedProbeAt_nil (rank : Nat) (env : Environment Row)
    (type : Ty Row) (obs : Observation Row) :
    MaskedProbeAt leRow rank env [] type obs ↔ ProbeAt leRow rank env type obs := by
  cases rank <;> rfl

@[simp] theorem maskedProbeAt_mask (rank : Nat) (env : Environment Row)
    (hidden more : List Nat) (type : Ty Row) (obs : Observation Row) :
    MaskedProbeAt leRow rank env hidden (.mask more type) obs ↔
      MaskedProbeAt leRow rank env (hidden ++ more) type obs := by
  cases rank <;> exact maskedProbeStep_mask hidden more type obs

@[simp] theorem probeAt_mask (rank : Nat) (env : Environment Row)
    (hidden : List Nat) (type : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.mask hidden type) obs ↔
      MaskedProbeAt leRow rank env hidden type obs := by
  rw [← maskedProbeAt_nil, maskedProbeAt_mask]
  rfl

/-- The independent interpretation applies to every demand and every
arbitrary producer assignment, not just a rigid or positive fragment. -/
theorem mask_parameter (type : Ty Row) (hidden : List Nat)
    (rank : Nat) (env : Environment Row) (demand : Demand Row) :
    AcceptAt leRow rank env (.mask hidden type) demand ↔
      MaskedAcceptAt leRow rank env hidden type demand := by
  unfold AcceptAt MaskedAcceptAt
  simp only [probeAt_mask]

theorem maskedProbeAt_congr (rank : Nat) (env : Environment Row)
    (first last : List Nat) (same : ∀ label, label ∈ first ↔ label ∈ last)
    (type : Ty Row) (obs : Observation Row) :
    MaskedProbeAt leRow rank env first type obs ↔
      MaskedProbeAt leRow rank env last type obs := by
  cases rank <;> exact maskedProbeStep_congr first last same type obs

theorem mask_composition (type : Ty Row) (first last : List Nat) :
    ProducerEq leRow (.mask last (.mask first type)) (.mask (first ++ last) type) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  rw [probeAt_mask, maskedProbeAt_mask, probeAt_mask]
  apply maskedProbeAt_congr
  intro label
  simp only [List.mem_append, or_comm]

theorem mask_nil (type : Ty Row) : ProducerEq leRow (.mask [] type) type := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  rw [probeAt_mask, maskedProbeAt_nil]

theorem mask_congr (first last : List Nat) (same : ∀ label, label ∈ first ↔ label ∈ last)
    (type : Ty Row) : ProducerEq leRow (.mask first type) (.mask last type) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  rw [probeAt_mask, probeAt_mask]
  exact maskedProbeAt_congr rank env first last same type obs

theorem mask_idempotent (type : Ty Row) (hidden : List Nat) :
    ProducerEq leRow (.mask hidden (.mask hidden type)) (.mask hidden type) :=
  producerEq_trans (mask_composition type hidden hidden)
    (mask_congr (hidden ++ hidden) hidden (by intro label; simp) type)

/-- Hiding a required head leaves only width; the payload is neither
inspected nor incorrectly declared to satisfy every requested payload. -/
theorem mask_required (label : Nat) (payload : Ty Row) (hidden : List Nat)
    (member : label ∈ hidden) :
    ProducerEq leRow (.mask hidden (required label payload)) .emptyRecord := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep, required, member]

/-- Outer masks do not cross a pair's payload boundary. -/
theorem mask_pair (hidden : List Nat) (first last : Ty Row) :
    ProducerEq leRow (.mask hidden (.pair first last)) (.pair first last) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

/-- A mask inside a variant payload stays inside; an outer mask leaves the
payload interpretation unchanged. -/
theorem mask_variant (hidden : List Nat) (label : Nat) (payload : Ty Row) :
    ProducerEq leRow (.mask hidden (.variant label payload)) (.variant label payload) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

theorem mask_arrow (hidden : List Nat) (input output : Ty Row) (inputRow outputRow : Row) :
    ProducerEq leRow (.mask hidden (.arrow input inputRow output outputRow))
      (.arrow input inputRow output outputRow) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

/-- Moving a payload mask outward is observably wrong, even in one finite
variant with an integer field and a single hidden label. -/
theorem payload_mask_not_outer (label tag : Nat) :
    ¬ ProducerEq leRow
      (.variant tag (.mask [label] (required label (.base .int))))
      (.mask [label] (.variant tag (required label (.base .int)))) := by
  intro same
  let env : Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  let obs : Observation Row := .variant tag (.field label (.base .int))
  have valid : ProbeAt leRow 0 env
      (.mask [label] (.variant tag (required label (.base .int)))) obs := by
    simp [ProbeAt, ProbeStep, MaskedProbeStep, obs, required]
  have invalid := (producerLe_iff_probe _ _).mp same.1 0 env obs valid
  simp [ProbeAt, ProbeStep, MaskedProbeStep, obs, required] at invalid

end Yulang.CommonNominalFinite
