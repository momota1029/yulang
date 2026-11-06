import Yulang.ProducerContextual
import Yulang.CorePresenceGenerationModel

/-!
# A concrete finite presence and contextual-demand carrier

The syntax and its recursive observation interpreter are independent of
constraint generation, typing and solving. Demand parameters name arbitrary
finite producer types, also inside negative arrow observations. The extra
optional observation is interpreted recursively; it does not reinterpret
producer subtyping as inclusion of runtime values.

An outer field mask remains at the current record layer. It accumulates
through record tails and default sources, but payloads restart with no mask.
The independent strict runtime readout and the regular closure are separate
modules. No law is stored in the carrier or its environment.
-/

namespace Yulang.CommonFinite

open Inference
open ProducerContextual (Head)

universe u
variable {Row : Type u}

inductive Ty (Row : Type u) where
  | base : Base → Ty Row
  | bottom : Ty Row
  | top : Ty Row
  | union : Ty Row → Ty Row → Ty Row
  | inter : Ty Row → Ty Row → Ty Row
  | pair : Ty Row → Ty Row → Ty Row
  | emptyRecord : Ty Row
  | exactEmpty : Ty Row
  | record : Nat → Ty Row → Ty Row → Ty Row
  | recordDefault : Nat → Ty Row → Ty Row → Ty Row
  | variant : Nat → Ty Row → Ty Row
  | arrow : Ty Row → Row → Ty Row → Row → Ty Row
  | mask : List Nat → Ty Row → Ty Row
  deriving Repr

def required (label : Nat) (payload : Ty Row) : Ty Row :=
  .record label payload .emptyRecord

structure Environment (Row : Type u) where
  types : Nat → Ty Row
  roles : Nat → List Head

inductive Observation (Row : Type u) where
  | trivial : Observation Row
  | impossible : Observation Row
  | base : Base → Observation Row
  | records : Observation Row
  | role : Nat → Observation Row
  | pairFirst : Observation Row → Observation Row
  | pairLast : Observation Row → Observation Row
  | field : Nat → Observation Row → Observation Row
  | optional : Nat → Observation Row → Observation Row
  | variant : Nat → Observation Row → Observation Row
  | arrowArgument : Nat → Observation Row
  | arrowResult : Observation Row → Observation Row
  | arrowInputRow : Row → Observation Row
  | arrowOutputRow : Row → Observation Row

/-- Masking a demanded field discards its payload demand, retaining record
shape. This operation is distinct from interpreting a masked producer. -/
def Observation.mask (hidden : List Nat) : Observation Row → Observation Row
  | .field label payload => if label ∈ hidden then .records else .field label payload
  | .optional label payload => if label ∈ hidden then .records else .optional label payload
  | other => other

/-- The mask is outer-layer state, not a recursive change to payload types.
A present head discharges its own demand and leaves only other demands to the
tail. Optional demands accept known absence; unknown width accepts only the
trivial optional payload. Default keeps all unrelated source observations. -/
def MaskedProbeStep (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) (hidden : List Nat) :
    Ty Row → Observation Row → Prop
  | _, .trivial => True
  | .bottom, _ => True
  | .top, _ => False
  | .union first last, obs =>
      MaskedProbeStep leRow env argumentOrder hidden first obs ∧
      MaskedProbeStep leRow env argumentOrder hidden last obs
  | .inter first last, obs =>
      MaskedProbeStep leRow env argumentOrder hidden first obs ∨
      MaskedProbeStep leRow env argumentOrder hidden last obs
  | .mask more source, obs =>
      MaskedProbeStep leRow env argumentOrder (hidden ++ more) source obs
  | .base actual, .base expected => actual = expected
  | .base actual, .role name => .base actual ∈ env.roles name
  | .pair _ _, .role name => .pair ∈ env.roles name
  | .emptyRecord, .role name => .records ∈ env.roles name
  | .exactEmpty, .role name => .records ∈ env.roles name
  | .record _ _ _, .role name => .records ∈ env.roles name
  | .recordDefault _ _ _, .role name => .records ∈ env.roles name
  | .variant label _, .role name => .variant label ∈ env.roles name
  | .arrow _ _ _ _, .role name => .arrow ∈ env.roles name
  | .pair first _, .pairFirst obs => MaskedProbeStep leRow env argumentOrder [] first obs
  | .pair _ last, .pairLast obs => MaskedProbeStep leRow env argumentOrder [] last obs
  | .emptyRecord, .records => True
  | .exactEmpty, .records => True
  | .record _ _ _, .records => True
  | .recordDefault _ _ _, .records => True
  | .emptyRecord, .optional _ obs => obs = .trivial
  | .exactEmpty, .optional label obs => label ∉ hidden ∨ obs = .trivial
  | .record current payload rest, .field label obs =>
      if label = current ∧ current ∉ hidden then
        MaskedProbeStep leRow env argumentOrder [] payload obs
      else MaskedProbeStep leRow env argumentOrder hidden rest (.field label obs)
  | .record current payload rest, .optional label obs =>
      if label = current ∧ current ∉ hidden then
        MaskedProbeStep leRow env argumentOrder [] payload obs
      else MaskedProbeStep leRow env argumentOrder hidden rest (.optional label obs) ∨ obs = .trivial
  | .recordDefault current source fallback, .field label obs =>
      if label = current ∧ current ∉ hidden then
        MaskedProbeStep leRow env argumentOrder hidden source (.optional label obs) ∧
          (MaskedProbeStep leRow env argumentOrder hidden source (.field label .trivial) ∨
            MaskedProbeStep leRow env argumentOrder [] fallback obs)
      else MaskedProbeStep leRow env argumentOrder hidden source (.field label obs)
  | .recordDefault current source fallback, .optional label obs =>
      (if label = current ∧ current ∉ hidden then
        MaskedProbeStep leRow env argumentOrder hidden source (.optional label obs) ∧
          (MaskedProbeStep leRow env argumentOrder hidden source (.field label .trivial) ∨
            MaskedProbeStep leRow env argumentOrder [] fallback obs)
      else MaskedProbeStep leRow env argumentOrder hidden source (.optional label obs)) ∨ obs = .trivial
  | .variant actual payload, .variant expected obs =>
      actual = expected ∧ MaskedProbeStep leRow env argumentOrder [] payload obs
  | .arrow input _ _ _, .arrowArgument name => argumentOrder (env.types name) input
  | .arrow _ _ output _, .arrowResult obs => MaskedProbeStep leRow env argumentOrder [] output obs
  | .arrow _ inputRow _ _, .arrowInputRow expected => leRow expected inputRow
  | .arrow _ _ _ outputRow, .arrowOutputRow expected => leRow outputRow expected
  | _, _ => False

def ProbeStep (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) : Ty Row → Observation Row → Prop :=
  MaskedProbeStep leRow env argumentOrder []

def ProbeAt (leRow : Row → Row → Prop) : Nat → Environment Row → Ty Row → Observation Row → Prop
  | 0, env => ProbeStep leRow env (fun _ _ => True)
  | rank + 1, env => ProbeStep leRow env (fun expected input =>
      ∀ next obs, ProbeAt leRow rank next input obs → ProbeAt leRow rank next expected obs)

def MaskedProbeAt (leRow : Row → Row → Prop) :
    Nat → Environment Row → List Nat → Ty Row → Observation Row → Prop
  | 0, env, hidden => MaskedProbeStep leRow env (fun _ _ => True) hidden
  | rank + 1, env, hidden => MaskedProbeStep leRow env (fun expected input =>
      ∀ next obs, ProbeAt leRow rank next input obs → ProbeAt leRow rank next expected obs) hidden

inductive Demand (Row : Type u) where
  | atom : Observation Row → Demand Row
  | inter : Demand Row → Demand Row → Demand Row
  | var : Nat → Demand Row
  | role : Nat → Demand Row
  | mask : List Nat → Demand Row → Demand Row
  | pair : Demand Row → Demand Row → Demand Row
  | required : Nat → Demand Row → Demand Row
  | optional : Nat → Demand Row → Demand Row
  | variant : Nat → Demand Row → Demand Row
  | arrow : Nat → Row → Demand Row → Row → Demand Row

def Demand.tests (leRow : Row → Row → Prop) (rank : Nat) (env : Environment Row) :
    Demand Row → Observation Row → Prop
  | .atom expected, obs => obs = expected
  | .inter first last, obs => first.tests leRow rank env obs ∨ last.tests leRow rank env obs
  | .var name, obs => ProbeAt leRow rank env (env.types name) obs
  | .role name, obs => obs = .role name
  | .mask hidden demand, obs =>
      ∃ inner, demand.tests leRow rank env inner ∧ obs = inner.mask hidden
  | .pair first last, obs =>
      obs = .pairFirst .trivial ∨ obs = .pairLast .trivial ∨
      (∃ inner, first.tests leRow rank env inner ∧ obs = .pairFirst inner) ∨
      (∃ inner, last.tests leRow rank env inner ∧ obs = .pairLast inner)
  | .required label payload, obs =>
      obs = .field label .trivial ∨
      ∃ inner, payload.tests leRow rank env inner ∧ obs = .field label inner
  | .optional label payload, obs =>
      obs = .records ∨ ∃ inner, payload.tests leRow rank env inner ∧ obs = .optional label inner
  | .variant label payload, obs =>
      obs = .variant label .trivial ∨
      ∃ inner, payload.tests leRow rank env inner ∧ obs = .variant label inner
  | .arrow input inputRow output outputRow, obs =>
      obs = .arrowArgument input ∨ obs = .arrowInputRow inputRow ∨
      obs = .arrowOutputRow outputRow ∨ obs = .arrowResult .trivial ∨
      ∃ inner, output.tests leRow rank env inner ∧ obs = .arrowResult inner

def AcceptAt (leRow : Row → Row → Prop) (rank : Nat) (env : Environment Row)
    (producer : Ty Row) (demand : Demand Row) : Prop :=
  ∀ obs, demand.tests leRow rank env obs → ProbeAt leRow rank env producer obs

/-- Independent outer-mask interpretation of demands: mask accumulation and
payload reset are specified by `MaskedProbeStep`, not by `AcceptAt (mask ...)`. -/
def MaskedAcceptAt (leRow : Row → Row → Prop) (rank : Nat) (env : Environment Row)
    (hidden : List Nat) (producer : Ty Row) (demand : Demand Row) : Prop :=
  ∀ obs, demand.tests leRow rank env obs → MaskedProbeAt leRow rank env hidden producer obs

def ProducerLeAt (leRow : Row → Row → Prop) (rank : Nat) (source target : Ty Row) : Prop :=
  ∀ env demand, AcceptAt leRow rank env target demand → AcceptAt leRow rank env source demand

def ProducerLe (leRow : Row → Row → Prop) (source target : Ty Row) : Prop :=
  ∀ rank, ProducerLeAt leRow rank source target

def ProducerEq (leRow : Row → Row → Prop) (source target : Ty Row) : Prop :=
  ProducerLe leRow source target ∧ ProducerLe leRow target source

variable {leRow : Row → Row → Prop} {env : Environment Row}
  {argumentOrder : Ty Row → Ty Row → Prop}

@[simp] theorem maskedProbeStep_union (hidden : List Nat)
    (first last : Ty Row) (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder hidden (.union first last) obs ↔
      MaskedProbeStep leRow env argumentOrder hidden first obs ∧
      MaskedProbeStep leRow env argumentOrder hidden last obs := by
  cases obs <;> simp [MaskedProbeStep]

@[simp] theorem maskedProbeStep_inter (hidden : List Nat)
    (first last : Ty Row) (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder hidden (.inter first last) obs ↔
      MaskedProbeStep leRow env argumentOrder hidden first obs ∨
      MaskedProbeStep leRow env argumentOrder hidden last obs := by
  cases obs <;> simp [MaskedProbeStep]

@[simp] theorem probeStep_union (first last : Ty Row) (obs : Observation Row) :
    ProbeStep leRow env argumentOrder (.union first last) obs ↔
      ProbeStep leRow env argumentOrder first obs ∧ ProbeStep leRow env argumentOrder last obs := by
  cases obs <;> simp [ProbeStep, MaskedProbeStep]

@[simp] theorem probeStep_inter (first last : Ty Row) (obs : Observation Row) :
    ProbeStep leRow env argumentOrder (.inter first last) obs ↔
      ProbeStep leRow env argumentOrder first obs ∨ ProbeStep leRow env argumentOrder last obs := by
  cases obs <;> simp [ProbeStep, MaskedProbeStep]

@[simp] theorem probeStep_bottom (obs : Observation Row) :
    ProbeStep leRow env argumentOrder (.bottom : Ty Row) obs := by
  cases obs <;> trivial

@[simp] theorem probeStep_trivial (type : Ty Row) :
    ProbeStep leRow env argumentOrder type .trivial := by
  cases type <;> trivial

@[simp] theorem probeAt_union (rank : Nat) (first last : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.union first last) obs ↔
      ProbeAt leRow rank env first obs ∧ ProbeAt leRow rank env last obs := by
  cases rank <;> exact probeStep_union first last obs

@[simp] theorem probeAt_inter (rank : Nat) (first last : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.inter first last) obs ↔
      ProbeAt leRow rank env first obs ∨ ProbeAt leRow rank env last obs := by
  cases rank <;> exact probeStep_inter first last obs

@[simp] theorem probeAt_bottom (rank : Nat) (obs : Observation Row) :
    ProbeAt leRow rank env (.bottom : Ty Row) obs := by
  cases rank <;> exact probeStep_bottom obs

@[simp] theorem probeAt_trivial (rank : Nat) (type : Ty Row) :
    ProbeAt leRow rank env type .trivial := by
  cases rank <;> exact probeStep_trivial type

@[simp] theorem acceptAt_atom (rank : Nat) (env : Environment Row) (type : Ty Row)
    (obs : Observation Row) :
    AcceptAt leRow rank env type (.atom obs) ↔ ProbeAt leRow rank env type obs := by
  simp [AcceptAt, Demand.tests]

@[simp] theorem acceptAt_var (rank : Nat) (env : Environment Row) (type : Ty Row) (name : Nat) :
    AcceptAt leRow rank env type (.var name) ↔
      ∀ obs, ProbeAt leRow rank env (env.types name) obs → ProbeAt leRow rank env type obs := Iff.rfl

@[simp] theorem acceptAt_role (rank : Nat) (env : Environment Row) (type : Ty Row) (name : Nat) :
    AcceptAt leRow rank env type (.role name) ↔ ProbeAt leRow rank env type (.role name) := by
  simp [AcceptAt, Demand.tests]

@[simp] theorem acceptAt_inter (rank : Nat) (env : Environment Row) (type : Ty Row)
    (first last : Demand Row) :
    AcceptAt leRow rank env type (.inter first last) ↔
      AcceptAt leRow rank env type first ∧ AcceptAt leRow rank env type last := by
  simp [AcceptAt, Demand.tests, or_imp, forall_and]

@[simp] theorem acceptAt_mask (rank : Nat) (env : Environment Row) (type : Ty Row)
    (hidden : List Nat) (demand : Demand Row) :
    AcceptAt leRow rank env type (.mask hidden demand) ↔
      ∀ obs, demand.tests leRow rank env obs → ProbeAt leRow rank env type (obs.mask hidden) := by
  constructor
  · intro accepted obs test
    exact accepted (obs.mask hidden) ⟨obs, test, rfl⟩
  · rintro accepted obs ⟨inner, test, rfl⟩
    exact accepted inner test

theorem producerLeAt_iff_probe (rank : Nat) (source target : Ty Row) :
    ProducerLeAt leRow rank source target ↔
      ∀ env obs, ProbeAt leRow rank env target obs → ProbeAt leRow rank env source obs := by
  constructor
  · intro below env obs accepted
    exact (acceptAt_atom rank env source obs).mp
      (below env (.atom obs) ((acceptAt_atom rank env target obs).mpr accepted))
  · intro below env demand accepted obs test
    exact below env obs (accepted obs test)

theorem producerLe_iff_probe (source target : Ty Row) :
    ProducerLe leRow source target ↔
      ∀ rank env obs, ProbeAt leRow rank env target obs → ProbeAt leRow rank env source obs :=
  forall_congr' fun rank => producerLeAt_iff_probe rank source target

theorem producerEq_iff_probe (source target : Ty Row) :
    ProducerEq leRow source target ↔
      ∀ rank env obs, ProbeAt leRow rank env source obs ↔ ProbeAt leRow rank env target obs := by
  constructor
  · intro same rank env obs
    exact ⟨(producerLe_iff_probe _ _).mp same.2 rank env obs,
      (producerLe_iff_probe _ _).mp same.1 rank env obs⟩
  · intro same
    exact ⟨(producerLe_iff_probe _ _).mpr (fun rank env obs => (same rank env obs).mpr),
      (producerLe_iff_probe _ _).mpr (fun rank env obs => (same rank env obs).mp)⟩

theorem producerLe_refl (type : Ty Row) : ProducerLe leRow type type :=
  fun _ _ _ accepted => accepted

theorem producerLe_trans {first middle last : Ty Row}
    (left : ProducerLe leRow first middle) (right : ProducerLe leRow middle last) :
    ProducerLe leRow first last :=
  fun rank env demand accepted => left rank env demand (right rank env demand accepted)

theorem producerEq_refl (type : Ty Row) : ProducerEq leRow type type :=
  ⟨producerLe_refl type, producerLe_refl type⟩

theorem producerEq_symm {first last : Ty Row} (same : ProducerEq leRow first last) :
    ProducerEq leRow last first := ⟨same.2, same.1⟩

theorem producerEq_trans {first middle last : Ty Row}
    (left : ProducerEq leRow first middle) (right : ProducerEq leRow middle last) :
    ProducerEq leRow first last :=
  ⟨producerLe_trans left.1 right.1, producerLe_trans right.2 left.2⟩

theorem pair_union_group (a b c d : Ty Row) :
    ProducerEq leRow (.union (.pair a b) (.pair c d))
      (.pair (.union a c) (.union b d)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

theorem record_union_group (label : Nat) (a rest b tail : Ty Row) :
    ProducerEq leRow (.union (.record label a rest) (.record label b tail))
      (.record label (.union a b) (.union rest tail)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split <;> try simp
  all_goals exact and_or_right.symm

theorem pair_union_first (a b c : Ty Row) :
    ProducerEq leRow (.pair (.union a b) c) (.union (.pair a c) (.pair b c)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

theorem pair_union_last (a b c : Ty Row) :
    ProducerEq leRow (.pair a (.union b c)) (.union (.pair a b) (.pair a c)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

theorem record_union_payload (label : Nat) (a b rest : Ty Row) :
    ProducerEq leRow (.record label (.union a b) rest)
      (.union (.record label a rest) (.record label b rest)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split <;> try simp
  all_goals exact and_or_right.symm

theorem variant_union (label : Nat) (a b : Ty Row) :
    ProducerEq leRow (.variant label (.union a b))
      (.union (.variant label a) (.variant label b)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep, and_and_and_comm]

@[simp] theorem probeAt_pairFirst (rank : Nat) (a b : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.pair a b) (.pairFirst obs) ↔ ProbeAt leRow rank env a obs := by
  cases rank <;> rfl

@[simp] theorem probeAt_pairLast (rank : Nat) (a b : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.pair a b) (.pairLast obs) ↔ ProbeAt leRow rank env b obs := by
  cases rank <;> rfl

@[simp] theorem probeAt_variant (rank : Nat) (actual expected : Nat)
    (payload : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.variant actual payload) (.variant expected obs) ↔
      actual = expected ∧ ProbeAt leRow rank env payload obs := by
  cases rank <;> rfl

/-- Every contextual payload demand is retained, including masks beneath a
constructor. No nonempty-payload premise or data-emptiness branch is needed. -/
theorem producerLe_pair_iff (a b c d : Ty Row) :
    ProducerLe leRow (.pair a b) (.pair c d) ↔
      ProducerLe leRow a c ∧ ProducerLe leRow b d := by
  constructor
  · intro below
    have test := (producerLe_iff_probe _ _).mp below
    constructor
    · apply (producerLe_iff_probe _ _).mpr
      intro rank env obs accepted
      exact (probeAt_pairFirst rank a b obs).mp
        (test rank env (.pairFirst obs) ((probeAt_pairFirst rank c d obs).mpr accepted))
    · apply (producerLe_iff_probe _ _).mpr
      intro rank env obs accepted
      exact (probeAt_pairLast rank a b obs).mp
        (test rank env (.pairLast obs) ((probeAt_pairLast rank c d obs).mpr accepted))
  · rintro ⟨first, last⟩
    have first := (producerLe_iff_probe _ _).mp first
    have last := (producerLe_iff_probe _ _).mp last
    apply (producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have first := first rank env
    have last := last rank env
    cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]

theorem producerLe_variant_iff (label : Nat) (a b : Ty Row) :
    ProducerLe leRow (.variant label a) (.variant label b) ↔ ProducerLe leRow a b := by
  constructor
  · intro below
    have test := (producerLe_iff_probe _ _).mp below
    apply (producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    exact ((probeAt_variant rank label label a obs).mp
      (test rank env (.variant label obs) ((probeAt_variant rank label label b obs).mpr ⟨rfl, accepted⟩))).2
  · intro below
    have test := (producerLe_iff_probe _ _).mp below
    apply (producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have test := test rank env
    cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]

theorem producerLe_record_mono (label : Nat) {a b rest tail : Ty Row}
    (payload : ProducerLe leRow a b) (remaining : ProducerLe leRow rest tail) :
    ProducerLe leRow (.record label a rest) (.record label b tail) := by
  have payload := (producerLe_iff_probe _ _).mp payload
  have remaining := (producerLe_iff_probe _ _).mp remaining
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  have payload := payload rank env
  have remaining := remaining rank env
  cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split <;> simp_all
  all_goals exact Or.imp (remaining _) id accepted

theorem producerLe_union_mono {a b c d : Ty Row}
    (left : ProducerLe leRow a b) (right : ProducerLe leRow c d) :
    ProducerLe leRow (.union a c) (.union b d) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  exact (probeAt_union _ _ _ _).mpr
    ⟨(producerLe_iff_probe _ _).mp left rank env obs ((probeAt_union _ _ _ _).mp accepted).1,
     (producerLe_iff_probe _ _).mp right rank env obs ((probeAt_union _ _ _ _).mp accepted).2⟩

theorem producerLe_inter_mono {a b c d : Ty Row}
    (left : ProducerLe leRow a b) (right : ProducerLe leRow c d) :
    ProducerLe leRow (.inter a c) (.inter b d) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  exact (probeAt_inter _ _ _ _).mpr (((probeAt_inter _ _ _ _).mp accepted).elim
    (fun valid => Or.inl ((producerLe_iff_probe _ _).mp left rank env obs valid))
    (fun valid => Or.inr ((producerLe_iff_probe _ _).mp right rank env obs valid)))

theorem producerLe_union_iff (a b c : Ty Row) :
    ProducerLe leRow (.union a b) c ↔ ProducerLe leRow a c ∧ ProducerLe leRow b c := by
  simp only [producerLe_iff_probe, probeAt_union, forall_and]

theorem producerLe_inter_iff (a b c : Ty Row) :
    ProducerLe leRow a (.inter b c) ↔ ProducerLe leRow a b ∧ ProducerLe leRow a c := by
  simp only [producerLe_iff_probe, probeAt_inter, or_imp, forall_and]

theorem producerLe_union_left (a b : Ty Row) : ProducerLe leRow a (.union a b) := by
  apply (producerLe_iff_probe _ _).mpr
  exact fun rank env obs accepted => ((probeAt_union rank a b obs).mp accepted).1

theorem producerLe_union_right (a b : Ty Row) : ProducerLe leRow b (.union a b) := by
  apply (producerLe_iff_probe _ _).mpr
  exact fun rank env obs accepted => ((probeAt_union rank a b obs).mp accepted).2

theorem producerEq_union_absorb {a b : Ty Row} (below : ProducerLe leRow a b) :
    ProducerEq leRow (.union a b) b :=
  ⟨(producerLe_union_iff _ _ _).mpr ⟨below, producerLe_refl b⟩, producerLe_union_right a b⟩

theorem producerEq_union {a b c d : Ty Row}
    (first : ProducerEq leRow a b) (last : ProducerEq leRow c d) :
    ProducerEq leRow (.union a c) (.union b d) :=
  ⟨producerLe_union_mono first.1 last.1, producerLe_union_mono first.2 last.2⟩

theorem producerEq_inter {a b c d : Ty Row}
    (first : ProducerEq leRow a b) (last : ProducerEq leRow c d) :
    ProducerEq leRow (.inter a c) (.inter b d) :=
  ⟨producerLe_inter_mono first.1 last.1, producerLe_inter_mono first.2 last.2⟩

theorem producerEq_pair {a b c d : Ty Row}
    (first : ProducerEq leRow a b) (last : ProducerEq leRow c d) :
    ProducerEq leRow (.pair a c) (.pair b d) :=
  ⟨(producerLe_pair_iff _ _ _ _).mpr ⟨first.1, last.1⟩,
    (producerLe_pair_iff _ _ _ _).mpr ⟨first.2, last.2⟩⟩

theorem producerEq_record (label : Nat) {a b rest tail : Ty Row}
    (payload : ProducerEq leRow a b) (remaining : ProducerEq leRow rest tail) :
    ProducerEq leRow (.record label a rest) (.record label b tail) :=
  ⟨producerLe_record_mono label payload.1 remaining.1,
    producerLe_record_mono label payload.2 remaining.2⟩

theorem producerEq_variant (label : Nat) {a b : Ty Row} (payload : ProducerEq leRow a b) :
    ProducerEq leRow (.variant label a) (.variant label b) :=
  ⟨(producerLe_variant_iff _ _ _).mpr payload.1, (producerLe_variant_iff _ _ _).mpr payload.2⟩

/-- Unknown demand arguments are instantiated by arbitrary types. There is
no closed-domain or density premise in this inversion. -/
theorem arrow_argument_inversion
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) : ProducerLe leRow input' input := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  let witness : Environment Row := ⟨fun _ => input', fun _ => []⟩
  have target : ProbeAt leRow (rank + 1) witness
      (.arrow input' inputRow' output' outputRow') (.arrowArgument 0) := fun _ _ valid => valid
  have source := (producerLe_iff_probe _ _).mp below (rank + 1) witness (.arrowArgument 0) target
  exact source env obs accepted

theorem arrow_result_inversion
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) : ProducerLe leRow output output' := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  have test := (producerLe_iff_probe _ _).mp below rank env (.arrowResult obs)
  cases rank <;> exact test accepted

theorem arrow_input_row_inversion (rowRefl : ∀ row, leRow row row)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) : leRow inputRow' inputRow :=
  (producerLe_iff_probe _ _).mp below 0 ⟨fun _ => .bottom, fun _ => []⟩
    (.arrowInputRow inputRow') (rowRefl inputRow')

theorem arrow_output_row_inversion (rowRefl : ∀ row, leRow row row)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) : leRow outputRow outputRow' :=
  (producerLe_iff_probe _ _).mp below 0 ⟨fun _ => .bottom, fun _ => []⟩
    (.arrowOutputRow outputRow') (rowRefl outputRow')

theorem producerLe_arrow (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (argument : ProducerLe leRow input' input) (incoming : leRow inputRow' inputRow)
    (result : ProducerLe leRow output output') (outgoing : leRow outputRow outputRow') :
    ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow') := by
  have argument := (producerLe_iff_probe _ _).mp argument
  have result := (producerLe_iff_probe _ _).mp result
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank with
  | zero =>
      cases obs with
      | trivial | arrowArgument => trivial
      | arrowResult obs => exact result 0 env obs accepted
      | arrowInputRow expected => exact rowTrans accepted incoming
      | arrowOutputRow expected => exact rowTrans outgoing accepted
      | role | impossible | base | records | pairFirst | pairLast | field | optional | variant => exact accepted
  | succ rank =>
      cases obs with
      | trivial => trivial
      | arrowArgument expected =>
          exact fun next obs valid => accepted next obs (argument rank next obs valid)
      | arrowResult obs => exact result (rank + 1) env obs accepted
      | arrowInputRow expected => exact rowTrans accepted incoming
      | arrowOutputRow expected => exact rowTrans outgoing accepted
      | role | impossible | base | records | pairFirst | pairLast | field | optional | variant => exact accepted

/-- Complete four-component decomposition for every finite target argument,
not merely an embedding of a closed negative syntactic type. -/
theorem producerLe_arrow_iff (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (input input' output output' : Ty Row) (inputRow inputRow' outputRow outputRow' : Row) :
    ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow') ↔
      ProducerLe leRow input' input ∧ leRow inputRow' inputRow ∧
        ProducerLe leRow output output' ∧ leRow outputRow outputRow' := by
  constructor
  · intro below
    exact ⟨arrow_argument_inversion below, arrow_input_row_inversion rowRefl below,
      arrow_result_inversion below, arrow_output_row_inversion rowRefl below⟩
  · rintro ⟨argument, incoming, result, outgoing⟩
    exact producerLe_arrow (leRow := leRow) rowTrans argument incoming result outgoing

theorem producerEq_arrow (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : Ty Row} (inputRow outputRow : Row)
    (argument : ProducerEq leRow input input') (result : ProducerEq leRow output output') :
    ProducerEq leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow output' outputRow) :=
  ⟨producerLe_arrow (leRow := leRow) rowTrans argument.2 (rowRefl _) result.1 (rowRefl _),
    producerLe_arrow (leRow := leRow) rowTrans argument.1 (rowRefl _) result.2 (rowRefl _)⟩

/-- Every operation has a concrete syntax and a concrete demand interpretation. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Core.PresenceGeneration.Model where
  Ty := Ty Row
  Row := Row
  base := .base
  bottom := .bottom
  top := .top
  union := .union
  inter := .inter
  pair := .pair
  emptyRecord := .emptyRecord
  exactEmpty := .exactEmpty
  required := required
  record := .record
  recordDefault := .recordDefault
  variant := .variant
  arrow := .arrow
  empty := empty
  join := join
  subTy := ProducerLe leRow
  subRow := leRow

end Yulang.CommonFinite
