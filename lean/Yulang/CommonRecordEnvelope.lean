import Yulang.CommonDefaultRecord

/-!
# Executable head inspection for arbitrary record targets

The role observation assigning every non-record head to a role detects exactly
whether a target can require anything that a record constructor cannot supply.
Only the finitely many outer heads occurring in the target are needed. Payload
references, including negative arrow children and regular blocks, are not
inspected or restricted.

This supplies the finite head guard of whole-default inspection. Field and
optional payload comparisons are deliberately separate obligations.
-/

namespace Yulang.CommonRecordEnvelope

open CommonSyntax (Layer)
open ProducerContextual (Head)

universe u v

variable {Row : Type u} {Index : Type v}

/-- Outer heads only: a tail below a record head cannot change the head's role.
The list is finite even when payload references point into regular graphs. -/
def heads : Layer Row Index → List Head
  | .bottom | .top => []
  | .union first last | .inter first last => heads first ++ heads last
  | .mask _ source => heads source
  | .base scalar => [.base scalar]
  | .pair _ _ => [.pair]
  | .emptyRecord | .exactEmpty | .record _ _ _ | .recordDefault _ _ _ => [.records]
  | .variant label _ => [.variant label]
  | .arrow _ _ _ _ => [.arrow]

/-- Evaluate the target's role formula with records false and every other
head true. A true result is incompatible with any record producer. -/
def outsideRecords : Layer Row Index → Bool
  | .bottom => true
  | .top => false
  | .union first last => outsideRecords first && outsideRecords last
  | .inter first last => outsideRecords first || outsideRecords last
  | .mask _ source => outsideRecords source
  | .emptyRecord | .exactEmpty | .record _ _ _ | .recordDefault _ _ _ => false
  | _ => true

theorem heads_map (rename : Index → Target) (source : Layer Row Index) :
    heads (source.map rename) = heads source := by
  induction source <;> simp_all [heads, Layer.map]

theorem outsideRecords_map (rename : Index → Target) (source : Layer Row Index) :
    outsideRecords (source.map rename) = outsideRecords source := by
  induction source <;> simp_all [outsideRecords, Layer.map]

/-- The finite role environment realizes the Boolean head test exactly. -/
theorem outsideRecords_role_exact (leRow : Row → Row → Prop)
    (env : CommonFinite.Environment Row)
    (argumentOrder : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)
    (assignment : Index → CommonFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (name : Nat) (source : Layer Row Index)
    (roles : ∀ head ∈ heads source, head ∈ env.roles name ↔ head ≠ .records) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt depth assignment) (.role name) ↔ outsideRecords source = true := by
  induction source generalizing hidden with
  | bottom => simp [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords]
  | top => simp [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords]
  | union first last before after =>
      have leftRoles : ∀ head ∈ heads first, head ∈ env.roles name ↔ head ≠ .records :=
        fun head member => roles head (by simp only [heads, List.mem_append]; exact Or.inl member)
      have rightRoles : ∀ head ∈ heads last, head ∈ env.roles name ↔ head ≠ .records :=
        fun head member => roles head (by simp only [heads, List.mem_append]; exact Or.inr member)
      simpa only [Layer.evalAt, CommonFinite.maskedProbeStep_union, outsideRecords,
        Bool.and_eq_true] using and_congr (before hidden leftRoles) (after hidden rightRoles)
  | inter first last before after =>
      have leftRoles : ∀ head ∈ heads first, head ∈ env.roles name ↔ head ≠ .records :=
        fun head member => roles head (by simp only [heads, List.mem_append]; exact Or.inl member)
      have rightRoles : ∀ head ∈ heads last, head ∈ env.roles name ↔ head ≠ .records :=
        fun head member => roles head (by simp only [heads, List.mem_append]; exact Or.inr member)
      simpa only [Layer.evalAt, CommonFinite.maskedProbeStep_inter, outsideRecords,
        Bool.or_eq_true] using or_congr (before hidden leftRoles) (after hidden rightRoles)
  | mask more source ih =>
      simpa only [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        ih (hidden ++ more) roles
  | recordDefault label source fallback ih =>
      have excluded := roles .records (by simp [heads])
      cases depth <;>
        simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using excluded
  | base scalar =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles (.base scalar) (by simp [heads])
  | pair first last =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles .pair (by simp [heads])
  | emptyRecord =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles .records (by simp [heads])
  | exactEmpty =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles .records (by simp [heads])
  | record label payload rest ih =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles .records (by simp [heads])
  | variant label payload =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles (.variant label) (by simp [heads])
  | arrow input inputRow output outputRow =>
      simpa [Layer.evalAt, CommonFinite.MaskedProbeStep, outsideRecords] using
        roles .arrow (by simp [heads])

/-- Every possible record field and optional test, with only a record head. -/
def finiteEnvelope : CommonFinite.Ty Row := .record 0 .bottom .bottom

def EnvelopeTest (env : CommonFinite.Environment Row) : CommonFinite.Observation Row → Prop
  | .trivial | .records | .field _ _ | .optional _ _ => True
  | .role name => .records ∈ env.roles name
  | _ => False

theorem finiteEnvelope_probe (leRow : Row → Row → Prop) (rank : Nat)
    (env : CommonFinite.Environment Row) (obs : CommonFinite.Observation Row) :
    CommonFinite.ProbeAt leRow rank env finiteEnvelope obs ↔ EnvelopeTest env obs := by
  cases rank <;> cases obs <;>
    simp [finiteEnvelope, EnvelopeTest, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
      CommonFinite.MaskedProbeStep]
  all_goals intro _; cases ‹CommonFinite.Observation Row› <;> trivial

/-- The head guard controls every observation, not only a finite probe list.
In particular it forces all accepted roles to include the record head. -/
theorem outsideRecords_false_probe (leRow : Row → Row → Prop)
    (env : CommonFinite.Environment Row)
    (argumentOrder : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)
    (assignment : Index → CommonFinite.Ty Row) (depth : Nat)
    (hidden : List Nat) (source : Layer Row Index) (obs : CommonFinite.Observation Row)
    (compatible : outsideRecords source = false)
    (accepted : CommonFinite.MaskedProbeStep leRow env argumentOrder hidden
      (source.evalAt depth assignment) obs) : EnvelopeTest env obs := by
  induction source generalizing hidden with
  | union first last before after =>
      have both := (CommonFinite.maskedProbeStep_union hidden _ _ obs).mp accepted
      by_cases left : outsideRecords first = false
      · exact before hidden left both.1
      · have right : outsideRecords last = false := by
          cases firstEq : outsideRecords first <;> cases lastEq : outsideRecords last <;>
            simp_all [outsideRecords]
        exact after hidden right both.2
  | inter first last before after =>
      have both : outsideRecords first = false ∧ outsideRecords last = false := by
        simpa only [outsideRecords, Bool.or_eq_false_iff] using compatible
      exact ((CommonFinite.maskedProbeStep_inter hidden _ _ obs).mp accepted).elim
        (before hidden both.1) (after hidden both.2)
  | mask more source ih =>
      exact ih (hidden ++ more) compatible (by
        cases obs <;> simp_all only [Layer.evalAt, CommonFinite.MaskedProbeStep])
  | recordDefault label source fallback ih =>
      cases depth <;> cases obs <;>
        simp_all [outsideRecords, Layer.evalAt, CommonFinite.MaskedProbeStep, EnvelopeTest]
  | _ => cases obs <;>
      simp_all [outsideRecords, Layer.evalAt, CommonFinite.MaskedProbeStep, EnvelopeTest]

/-- Exact all-rank/all-environment head inspection for an arbitrary finite
outer layer and arbitrary payload assignment. -/
theorem finiteEnvelope_below_iff (leRow : Row → Row → Prop)
    (assignment : Index → CommonFinite.Ty Row) (depth : Nat) (target : Layer Row Index) :
    CommonFinite.ProducerLe leRow finiteEnvelope (target.evalAt depth assignment) ↔
      outsideRecords target = false := by
  constructor
  · intro below
    cases outside : outsideRecords target with
    | false => rfl
    | true =>
      apply False.elim
      let env : CommonFinite.Environment Row :=
        ⟨fun _ => .bottom, fun _ => (heads target).filter (fun head => decide (head ≠ .records))⟩
      have roles : ∀ head ∈ heads target, head ∈ env.roles 0 ↔ head ≠ .records := by
        intro head member
        simp only [env, List.mem_filter, decide_eq_true_eq]
        exact and_iff_right member
      have accepted : CommonFinite.ProbeAt leRow 0 env (target.evalAt depth assignment) (.role 0) :=
        (outsideRecords_role_exact leRow env (fun _ _ => True) assignment depth [] 0 target roles).mpr outside
      have rejected := (finiteEnvelope_probe leRow 0 env (.role 0)).mp
        ((CommonFinite.producerLe_iff_probe _ _).mp below 0 env (.role 0) accepted)
      simp [EnvelopeTest, env] at rejected
  · intro compatible
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    apply (finiteEnvelope_probe leRow rank env obs).mpr
    cases rank <;>
      exact outsideRecords_false_probe leRow env _ assignment depth [] target obs compatible accepted

/-- A regular common representative for all record-shaped observations. -/
def envelope : Common.Ty := Common.record 0 .bottom .bottom

@[simp] theorem envelope_observe (depth : Nat) : Common.observeTy depth envelope = finiteEnvelope := by
  cases depth <;> rfl

/-- Full common target head inspection. Neither its children nor its regular
references are restricted; all constructor depths are covered. -/
theorem envelope_below_iff (target : Common.Ty) :
    Common.Subtype envelope target ↔ outsideRecords target = false := by
  constructor
  · intro below
    apply (finiteEnvelope_below_iff Common.rowLe _ 0 target).mp
    have first := below 0
    rw [envelope_observe] at first
    exact first
  · intro compatible depth
    rw [envelope_observe]
    exact (finiteEnvelope_below_iff Common.rowLe _ depth target).mpr compatible

theorem envelope_below_default (label : Nat) (source fallback : Common.Ty) :
    Common.Subtype envelope (Common.recordDefault label source fallback) :=
  (envelope_below_iff _).mpr rfl

/-- Every valid whole-default target passes the actual finite Boolean guard. -/
theorem default_target_compatible (label : Nat) (source fallback target : Common.Ty)
    (below : Common.Subtype (Common.recordDefault label source fallback) target) :
    outsideRecords target = false :=
  (envelope_below_iff target).mp
    (Common.subtype_trans (envelope_below_default label source fallback) below)

end Yulang.CommonRecordEnvelope
