import Yulang.CommonFinite

/-!
# Dedicated nested nominal finite observations

Nominals retain their declaration ID, ordered arity and argument kinds. The
value arguments recursively use this extended carrier. Lower and upper probes
are interpreted independently at every negative rank. No structural tag is
used to encode nominal identity. Source typing and solver preservation are
separate obligations.
-/

namespace Yulang.CommonNominalFinite

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
  | nominal : Nat → List (Ty Row ⊕ Row) → Ty Row
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
  | nominalHead : Nat → Nat → Observation Row
  | nominalLower : Nat → Nat → Observation Row
  | nominalUpper : Nat → Nat → Observation Row
  | nominalRowLower : Nat → Row → Observation Row
  | nominalRowUpper : Nat → Row → Observation Row

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
  | .nominal actual arguments, .nominalHead expected arity =>
      actual = expected ∧ arguments.length = arity
  | .nominal _ arguments, .nominalLower index name =>
      ∃ actual, arguments[index]? = some (.inl actual) ∧ argumentOrder (env.types name) actual
  | .nominal _ arguments, .nominalUpper index name =>
      ∃ actual, arguments[index]? = some (.inl actual) ∧ argumentOrder actual (env.types name)
  | .nominal _ arguments, .nominalRowLower index expected =>
      ∃ actual, arguments[index]? = some (.inr actual) ∧ leRow expected actual
  | .nominal _ arguments, .nominalRowUpper index expected =>
      ∃ actual, arguments[index]? = some (.inr actual) ∧ leRow actual expected
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

end Yulang.CommonNominalFinite

namespace Yulang.CommonNominalFinite

variable {Row : Type u} {leRow : Row → Row → Prop}

def ArgumentEquivalent : (Ty Row ⊕ Row) → (Ty Row ⊕ Row) → Prop
  | .inl first, .inl last => ProducerEq leRow first last
  | .inr first, .inr last => leRow first last ∧ leRow last first
  | _, _ => False

def ArgumentsEquivalent (first last : List (Ty Row ⊕ Row)) : Prop :=
  ∀ (index : Nat) (a b : Ty Row ⊕ Row), first[index]? = some a → last[index]? = some b →
    ArgumentEquivalent (leRow := leRow) a b

theorem nominal_invariant_forward
    (rowRefl : ∀ row, leRow row row) (name other : Nat)
    (first last : List (Ty Row ⊕ Row))
    (below : ProducerLe leRow (.nominal name first) (.nominal other last)) :
    name = other ∧ first.length = last.length ∧
      ArgumentsEquivalent (leRow := leRow) first last := by
  have probes := (producerLe_iff_probe _ _).mp below
  let environment : Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have head := probes 0 environment (.nominalHead other last.length) ⟨rfl, rfl⟩
  change name = other ∧ first.length = last.length at head
  refine ⟨head.1, head.2, ?_⟩
  intro index a b left right
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have compare (upper : Bool) (rank : Nat) :
              ∀ env obs, ProbeAt leRow rank env (if upper then b else a) obs →
                ProbeAt leRow rank env (if upper then a else b) obs := by
            let env : Environment Row := ⟨fun _ => b, fun _ => []⟩
            cases upper with
            | false =>
                have accepted : ProbeAt leRow (rank + 1) env (.nominal other last)
                    (.nominalLower index 0) := by
                  exact ⟨b, right, fun _ _ accepted => accepted⟩
                have supplied := probes (rank + 1) env (.nominalLower index 0) accepted
                change ∃ actual, first[index]? = some (.inl actual) ∧
                  (∀ env obs, ProbeAt leRow rank env actual obs →
                    ProbeAt leRow rank env b obs) at supplied
                obtain ⟨actual, found, order⟩ := supplied
                have equal : actual = a := by simpa [left] using found.symm
                subst actual
                exact order
            | true =>
                have accepted : ProbeAt leRow (rank + 1) env (.nominal other last)
                    (.nominalUpper index 0) := by
                  exact ⟨b, right, fun _ _ accepted => accepted⟩
                have supplied := probes (rank + 1) env (.nominalUpper index 0) accepted
                change ∃ actual, first[index]? = some (.inl actual) ∧
                  (∀ env obs, ProbeAt leRow rank env b obs →
                    ProbeAt leRow rank env actual obs) at supplied
                obtain ⟨actual, found, order⟩ := supplied
                have equal : actual = a := by simpa [left] using found.symm
                subst actual
                exact order
          exact ⟨(producerLe_iff_probe _ _).mpr (compare true),
            (producerLe_iff_probe _ _).mpr (compare false)⟩
      | inr b =>
          have accepted : ProbeAt leRow 0 environment (.nominal other last)
              (.nominalRowUpper index b) := ⟨b, right, rowRefl b⟩
          have supplied := probes 0 environment (.nominalRowUpper index b) accepted
          change ∃ actual, first[index]? = some (.inr actual) ∧ leRow actual b at supplied
          simp [left] at supplied
  | inr a =>
      cases b with
      | inl b =>
          have accepted : ProbeAt leRow 0 environment (.nominal other last)
              (.nominalUpper index 0) := ⟨b, right, trivial⟩
          have supplied := probes 0 environment (.nominalUpper index 0) accepted
          change ∃ actual, first[index]? = some (.inl actual) ∧ True at supplied
          simp [left] at supplied
      | inr b =>
          have upper := probes 0 environment (.nominalRowUpper index b)
            (show ProbeAt leRow 0 environment (.nominal other last)
              (.nominalRowUpper index b) from ⟨b, right, rowRefl b⟩)
          have lower := probes 0 environment (.nominalRowLower index b)
            (show ProbeAt leRow 0 environment (.nominal other last)
              (.nominalRowLower index b) from ⟨b, right, rowRefl b⟩)
          change ∃ actual, first[index]? = some (.inr actual) ∧ leRow actual b at upper
          change ∃ actual, first[index]? = some (.inr actual) ∧ leRow b actual at lower
          simpa [ArgumentEquivalent, left] using And.intro upper lower

end Yulang.CommonNominalFinite

namespace Yulang.CommonNominalFinite

variable {Row : Type u} {leRow : Row → Row → Prop}

theorem arguments_at {first last : List (Ty Row ⊕ Row)}
    (size : first.length = last.length)
    (same : ArgumentsEquivalent (leRow := leRow) first last)
    {index : Nat} {actual : Ty Row ⊕ Row} (found : last[index]? = some actual) :
    ∃ previous, first[index]? = some previous ∧
      ArgumentEquivalent (leRow := leRow) previous actual := by
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp found
  have previousBound : index < first.length := by omega
  refine ⟨first[index], by simp [previousBound], ?_⟩
  exact same index _ actual (by simp [previousBound])
    (List.getElem?_eq_some_iff.mpr ⟨bound, selected⟩)

theorem nominal_probe_backward
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {name other : Nat} {first last : List (Ty Row ⊕ Row)}
    (identity : name = other) (size : first.length = last.length)
    (same : ArgumentsEquivalent (leRow := leRow) first last)
    {argumentOrder : Ty Row → Ty Row → Prop}
    (stable : ∀ a b, ProducerEq leRow a b → ∀ expected,
      (argumentOrder b expected → argumentOrder a expected) ∧
      (argumentOrder expected b → argumentOrder expected a))
    (env : Environment Row) (hidden : List Nat) (obs : Observation Row)
    (accepted : MaskedProbeStep leRow env argumentOrder hidden (.nominal other last) obs) :
    MaskedProbeStep leRow env argumentOrder hidden (.nominal name first) obs := by
  cases obs <;> simp only [MaskedProbeStep] at accepted ⊢
  all_goals first | contradiction | trivial | skip
  case nominalHead expected arity => exact ⟨identity.trans accepted.1, size.trans accepted.2⟩
  case nominalLower index parameter =>
    obtain ⟨actual, found, below⟩ := accepted
    obtain ⟨previous, previousAt, equivalent⟩ := arguments_at size same found
    cases previous with
    | inl previous =>
        exact ⟨previous, previousAt, (stable previous actual equivalent (env.types parameter)).2 below⟩
    | inr previous => exact False.elim equivalent
  case nominalUpper index parameter =>
    obtain ⟨actual, found, below⟩ := accepted
    obtain ⟨previous, previousAt, equivalent⟩ := arguments_at size same found
    cases previous with
    | inl previous =>
        exact ⟨previous, previousAt, (stable previous actual equivalent (env.types parameter)).1 below⟩
    | inr previous => exact False.elim equivalent
  case nominalRowLower index expected =>
    obtain ⟨actual, found, below⟩ := accepted
    obtain ⟨previous, previousAt, equivalent⟩ := arguments_at size same found
    cases previous with
    | inl previous => exact False.elim equivalent
    | inr previous => exact ⟨previous, previousAt, rowTrans below equivalent.2⟩
  case nominalRowUpper index expected =>
    obtain ⟨actual, found, below⟩ := accepted
    obtain ⟨previous, previousAt, equivalent⟩ := arguments_at size same found
    cases previous with
    | inl previous => exact False.elim equivalent
    | inr previous => exact ⟨previous, previousAt, rowTrans equivalent.1 below⟩

theorem nominal_invariant_backward
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {name other : Nat} {first last : List (Ty Row ⊕ Row)}
    (identity : name = other) (size : first.length = last.length)
    (same : ArgumentsEquivalent (leRow := leRow) first last) :
    ProducerLe leRow (.nominal name first) (.nominal other last) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank with
  | zero =>
      exact nominal_probe_backward (leRow := leRow) (argumentOrder := fun _ _ => True) rowTrans identity size same
        (fun _ _ _ _ => ⟨id, id⟩) env [] obs accepted
  | succ rank =>
      apply nominal_probe_backward (leRow := leRow)
        (argumentOrder := fun expected input => ∀ next obs,
          ProbeAt leRow rank next input obs → ProbeAt leRow rank next expected obs)
        rowTrans identity size same _ env [] obs accepted
      intro a b equivalent expected
      constructor
      · intro before next obs accepted
        exact (producerLe_iff_probe _ _).mp equivalent.1 rank next obs
          (before next obs accepted)
      · intro after next obs accepted
        apply after next obs
        exact (producerLe_iff_probe _ _).mp equivalent.2 rank next obs accepted

/-- Nested finite nominal applications over arbitrary rows. The head and every
argument direction are observed; invariance is a theorem of the demand order. -/
theorem nominal_finite_invariant_exact
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (name other : Nat) (first last : List (Ty Row ⊕ Row)) :
    ProducerLe leRow (.nominal name first) (.nominal other last) ↔
      name = other ∧ first.length = last.length ∧
      ArgumentsEquivalent (leRow := leRow) first last :=
  ⟨nominal_invariant_forward rowRefl name other first last,
    fun ⟨identity, size, same⟩ => nominal_invariant_backward (leRow := leRow) rowTrans identity size same⟩

end Yulang.CommonNominalFinite
