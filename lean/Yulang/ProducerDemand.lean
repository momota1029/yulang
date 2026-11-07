import Yulang.StructuralBase

/-!
# Producer order determined by union-free demands

These observations are requirements on finite structural producers, not data
membership. A constructor with a bottom payload still has its own shape.
Demand variables denote finite conjunctions of rigid observations, never
arbitrary predicates on producer syntax. Masks erase outer field requirements;
payload demands can have their own masks before placement under a constructor.
This finite interpretation of variables is a candidate, not a claim that all
symbolic unknown requirements are expressible by these observations. The
mixed-base/top boundary and the question about richer variable meanings are
documented in `notes/questions/2026-11-07-demand-model-contracts.md`, Q5.

Arrow argument observations use the old structural order on closed union-free
argument requirements. This proves preservation of all old finite structural
subtypes, with real arrows and rows, but does not yet prove new-order
contravariance for arbitrary arrow arguments or complete regular inference.
`ProducerRanked` supplies new-order arrow congruence for this same observer
grammar; it does not silently enlarge the variable interpretation.
-/

namespace Yulang.ProducerDemand

open Yulang.Inference
open StructuralBase

/-- Closed union-free argument requirements. -/
inductive Negative (Row : Type u) where
  | bottom : Negative Row
  | top : Negative Row
  | base : Base → Negative Row
  | inter : Negative Row → Negative Row → Negative Row
  | pair : Negative Row → Negative Row → Negative Row
  | records : Negative Row
  | field : Nat → Negative Row → Negative Row → Negative Row
  | variant : Nat → Negative Row → Negative Row
  | arrow : Negative Row → Row → Negative Row → Row → Negative Row

def Negative.embed : Negative Row → Ty Row
  | .bottom => .bottom
  | .top => .top
  | .base name => .base name
  | .inter a b => .inter a.embed b.embed
  | .pair a b => .pair a.embed b.embed
  | .records => .emptyRecord
  | .field label value rest => .record label value.embed rest.embed
  | .variant label value => .variant label value.embed
  | .arrow input inputRow output outputRow => .arrow input.embed inputRow output.embed outputRow

/-- Rigid requirement paths. There is no disjunction or producer-syntax test. -/
inductive Observation (Row : Type u) where
  | trivial : Observation Row
  | impossible : Observation Row
  | base : Base → Observation Row
  | records : Observation Row
  | pairFirst : Observation Row → Observation Row
  | pairLast : Observation Row → Observation Row
  | field : Nat → Observation Row → Observation Row
  | variant : Nat → Observation Row → Observation Row
  | arrowArgument : Negative Row → Observation Row
  | arrowResult : Observation Row → Observation Row
  | arrowInputRow : Row → Observation Row
  | arrowOutputRow : Row → Observation Row

/-- Erase an outer field requirement, retaining payload-local observations. -/
def Observation.mask (hidden : List Nat) : Observation Row → Observation Row
  | .field label value => if label ∈ hidden then .records else .field label value
  | other => other

/-- Independent producer-to-rigid-demand acceptance. -/
def Probe (leRow : Row → Row → Prop) : Ty Row → Observation Row → Prop
  | _, .trivial => True
  | .bottom, _ => True
  | .top, _ => False
  | .union a b, obs => Probe leRow a obs ∧ Probe leRow b obs
  | .inter a b, obs => Probe leRow a obs ∨ Probe leRow b obs
  | .base actual, .base expected => actual = expected
  | .pair a _, .pairFirst obs => Probe leRow a obs
  | .pair _ b, .pairLast obs => Probe leRow b obs
  | .emptyRecord, .records => True
  | .record _ _ _, .records => True
  | .record current value rest, .field label obs =>
      if label = current then Probe leRow value obs else Probe leRow rest (.field label obs)
  | .variant actual value, .variant expected obs => actual = expected ∧ Probe leRow value obs
  | .arrow input _ _ _, .arrowArgument expected => Subtype leRow expected.embed input
  | .arrow _ _ output _, .arrowResult obs => Probe leRow output obs
  | .arrow _ inputRow _ _, .arrowInputRow expected => leRow expected inputRow
  | .arrow _ _ _ outputRow, .arrowOutputRow expected => leRow outputRow expected
  | _, _ => False

/-- Union-free grammar, including symbolic variables beneath rigid
constructors. `Observation` supplies singleton rigid tests as well. -/
inductive Demand (Row : Type u) where
  | atom : Observation Row → Demand Row
  | inter : Demand Row → Demand Row → Demand Row
  | var : Nat → Demand Row
  | mask : List Nat → Demand Row → Demand Row
  | pair : Demand Row → Demand Row → Demand Row
  | required : Nat → Demand Row → Demand Row
  | variant : Nat → Demand Row → Demand Row
  | arrow : Negative Row → Row → Demand Row → Row → Demand Row

abbrev Environment (Row : Type u) := Nat → List (Observation Row)

def Demand.observations (env : Environment Row) : Demand Row → List (Observation Row)
  | .atom obs => [obs]
  | .inter a b => a.observations env ++ b.observations env
  | .var name => env name
  | .mask hidden demand => (demand.observations env).map (Observation.mask hidden)
  | .pair first last => [.pairFirst .trivial, .pairLast .trivial] ++
      (first.observations env).map Observation.pairFirst ++
      (last.observations env).map Observation.pairLast
  | .required label value => .field label .trivial ::
      (value.observations env).map (Observation.field label)
  | .variant label value => .variant label .trivial ::
      (value.observations env).map (Observation.variant label)
  | .arrow input inputRow output outputRow =>
      [.arrowArgument input, .arrowInputRow inputRow, .arrowOutputRow outputRow,
        .arrowResult .trivial] ++ (output.observations env).map Observation.arrowResult

/-- Place each requirement beneath a rigid constructor, including already
masked requirements. The instantiated result is again a union-free demand. -/
def Demand.project (project : Observation Row → Observation Row) (env : Environment Row)
    (demand : Demand Row) : Demand Row :=
  (demand.observations env).foldr (fun obs rest => .inter (.atom (project obs)) rest)
    (.atom (project .trivial))


def Accept (leRow : Row → Row → Prop) (env : Environment Row)
    (producer : Ty Row) (demand : Demand Row) : Prop :=
  ∀ obs ∈ demand.observations env, Probe leRow producer obs

/-- Decision 46: producer comparison is defined by accepted demands alone. -/
def ProducerLe (leRow : Row → Row → Prop) (source target : Ty Row) : Prop :=
  ∀ env demand, Accept leRow env target demand → Accept leRow env source demand

def ProducerEq (leRow : Row → Row → Prop) (source target : Ty Row) : Prop :=
  ProducerLe leRow source target ∧ ProducerLe leRow target source

variable {Row : Type u} {leRow : Row → Row → Prop}

@[simp] theorem accept_atom (env : Environment Row) (type : Ty Row) (obs : Observation Row) :
    Accept leRow env type (.atom obs) ↔ Probe leRow type obs := by
  simp [Accept, Demand.observations]

@[simp] theorem accept_inter (env : Environment Row) (type : Ty Row) (a b : Demand Row) :
    Accept leRow env type (.inter a b) ↔ Accept leRow env type a ∧ Accept leRow env type b := by
  simp [Accept, Demand.observations, or_imp, forall_and]

theorem producerLe_iff_probe (source target : Ty Row) :
    ProducerLe leRow source target ↔ ∀ obs, Probe leRow target obs → Probe leRow source obs := by
  constructor
  · intro h obs accept
    exact (accept_atom (fun _ => []) source obs).mp
      (h (fun _ => []) (.atom obs) ((accept_atom (fun _ => []) target obs).mpr accept))
  · intro h env demand accept obs member
    exact h obs (accept obs member)

theorem producerEq_iff_probe (source target : Ty Row) :
    ProducerEq leRow source target ↔ ∀ obs, Probe leRow source obs ↔ Probe leRow target obs := by
  simp only [ProducerEq, producerLe_iff_probe]
  constructor
  · rintro ⟨h, h'⟩ obs
    exact ⟨h' obs, h obs⟩
  · intro h
    exact ⟨fun obs => (h obs).mpr, fun obs => (h obs).mp⟩

theorem producerLe_refl (type : Ty Row) : ProducerLe leRow type type := by
  intro _ _ h
  exact h

theorem producerLe_trans {a b c : Ty Row}
    (hab : ProducerLe leRow a b) (hbc : ProducerLe leRow b c) : ProducerLe leRow a c := by
  intro env demand h
  exact hab env demand (hbc env demand h)

theorem producerEq_refl (type : Ty Row) : ProducerEq leRow type type :=
  ⟨producerLe_refl type, producerLe_refl type⟩

theorem producerEq_symm {a b : Ty Row} (h : ProducerEq leRow a b) : ProducerEq leRow b a :=
  ⟨h.2, h.1⟩

theorem producerEq_trans {a b c : Ty Row}
    (hab : ProducerEq leRow a b) (hbc : ProducerEq leRow b c) : ProducerEq leRow a c :=
  ⟨producerLe_trans hab.1 hbc.1, producerLe_trans hbc.2 hab.2⟩

@[simp] theorem probe_union (a b : Ty Row) (obs : Observation Row) :
    Probe leRow (.union a b) obs ↔ Probe leRow a obs ∧ Probe leRow b obs := by
  cases obs <;> simp [Probe]

@[simp] theorem probe_inter (a b : Ty Row) (obs : Observation Row) :
    Probe leRow (.inter a b) obs ↔ Probe leRow a obs ∨ Probe leRow b obs := by
  cases obs <;> simp [Probe]

@[simp] theorem probe_bottom (obs : Observation Row) : Probe leRow (.bottom : Ty Row) obs := by
  cases obs <;> trivial

@[simp] theorem probe_trivial (type : Ty Row) : Probe leRow type .trivial := by
  cases type <;> trivial

theorem probe_isRecord (h : IsRecord type) : Probe leRow type .records := by
  cases h <;> trivial

theorem probe_record_field (h : IsRecord type) (label : Nat) (obs : Observation Row) :
    Probe leRow type (.field label obs) ↔
      ∃ value, type.lookup label = some value ∧ Probe leRow value obs := by
  induction h with
  | empty => simp [Probe, Ty.lookup]
  | @field rest current value hr ih =>
      by_cases same : label = current
      · simp [Probe, Ty.lookup, same]
      · simpa [Probe, Ty.lookup, same] using ih

/-- Every old structural subtype preserves all new demands. Only row-order
transitivity is needed; reflexivity and antisymmetry are not assumptions. -/
theorem structural_subtype_preserved
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {source target : Ty Row} (h : Subtype leRow source target) :
    ProducerLe leRow source target := by
  apply (producerLe_iff_probe source target).mpr
  induction h with
  | refl => exact fun _ h => h
  | trans _ _ ih₁ ih₂ => exact fun obs h => ih₁ obs (ih₂ obs h)
  | bottom => exact fun obs _ => probe_bottom obs
  | top => intro obs; cases obs <;> simp [Probe]
  | unionLeft => intro obs h; exact ((probe_union _ _ obs).mp h).1
  | unionRight => intro obs h; exact ((probe_union _ _ obs).mp h).2
  | unionElim _ _ ih₁ ih₂ =>
      intro obs h
      exact (probe_union _ _ obs).mpr ⟨ih₁ obs h, ih₂ obs h⟩
  | interLeft => intro obs h; exact (probe_inter _ _ obs).mpr (.inl h)
  | interRight => intro obs h; exact (probe_inter _ _ obs).mpr (.inr h)
  | interIntro _ _ ih₁ ih₂ =>
      intro obs h
      exact ((probe_inter _ _ obs).mp h).elim (ih₁ obs) (ih₂ obs)
  | pair _ _ ih₁ ih₂ =>
      intro obs h
      cases obs <;> simp_all [Probe]
  | variant _ ih =>
      intro obs h
      cases obs <;> simp_all [Probe]
  | @arrow input' input inputRow' inputRow output output' outputRow outputRow'
      hi hir ho hor ihi iho =>
      intro obs h
      cases obs with
      | trivial => trivial
      | arrowArgument expected => exact Subtype.trans h hi
      | arrowResult obs => exact iho obs h
      | arrowInputRow expected => exact rowTrans h hir
      | arrowOutputRow expected => exact rowTrans hor h
      | impossible | base | records | pairFirst | pairLast | field | variant => exact h
  | @record source target hs ht fields subtype ih =>
      intro obs h
      cases obs with
      | trivial => exact probe_trivial source
      | records => exact probe_isRecord hs
      | field label obs =>
          obtain ⟨expected, he, hp⟩ := (probe_record_field ht label obs).mp h
          obtain ⟨actual, ha⟩ := fields label expected he
          exact (probe_record_field hs label obs).mpr
            ⟨actual, ha, ih label actual expected ha he obs hp⟩
      | impossible | base | pairFirst | pairLast | variant | arrowArgument | arrowResult
        | arrowInputRow | arrowOutputRow => cases ht <;> simp_all [Probe]

/-- Same-constructor unions group both components. The law follows from rigid
requirements, without adding a distribution rule to structural subtyping. -/
theorem pair_union_group (a b c d : Ty Row) :
    ProducerEq leRow (.union (.pair a b) (.pair c d))
      (.pair (.union a c) (.union b d)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro obs
  cases obs <;> simp [Probe]

theorem pair_union_first (a b c : Ty Row) :
    ProducerEq leRow (.pair (.union a b) c) (.union (.pair a c) (.pair b c)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro obs
  cases obs <;> simp [Probe]

theorem pair_union_last (a b c : Ty Row) :
    ProducerEq leRow (.pair a (.union b c)) (.union (.pair a b) (.pair a c)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro obs
  cases obs <;> simp [Probe]

/-- Identical first labels group payloads and arbitrary finite tails, preserving
first-field-wins. -/
theorem record_union_group (label : Nat) (a rest b tail : Ty Row) :
    ProducerEq leRow (.union (.record label a rest) (.record label b tail))
      (.record label (.union a b) (.union rest tail)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro obs
  cases obs <;> simp [Probe]
  case field name value => split <;> simp [*]

theorem record_union_payload (label : Nat) (a b rest : Ty Row) :
    ProducerEq leRow (.record label (.union a b) rest)
      (.union (.record label a rest) (.record label b rest)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro obs
  cases obs <;> simp [Probe]
  case field name value => split <;> simp [*]

theorem variant_union (label : Nat) (a b : Ty Row) :
    ProducerEq leRow (.variant label (.union a b))
      (.union (.variant label a) (.variant label b)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro obs
  cases obs <;> simp [Probe, and_assoc, and_left_comm]

/-- Constructor inversion keeps every payload observation, including
observations obtained by masking a payload demand before projection. -/
theorem producerLe_pair_iff (a b c d : Ty Row) :
    ProducerLe leRow (.pair a b) (.pair c d) ↔
      ProducerLe leRow a c ∧ ProducerLe leRow b d := by
  constructor
  · intro h
    have test := (producerLe_iff_probe _ _).mp h
    constructor
    · apply (producerLe_iff_probe _ _).mpr
      intro obs h
      exact test (.pairFirst obs) h
    · apply (producerLe_iff_probe _ _).mpr
      intro obs h
      exact test (.pairLast obs) h
  · rintro ⟨first, last⟩
    have first := (producerLe_iff_probe _ _).mp first
    have last := (producerLe_iff_probe _ _).mp last
    apply (producerLe_iff_probe _ _).mpr
    intro obs h
    cases obs <;> simp_all [Probe]

theorem producerLe_variant_iff (label : Nat) (a b : Ty Row) :
    ProducerLe leRow (.variant label a) (.variant label b) ↔ ProducerLe leRow a b := by
  constructor
  · intro h
    have test := (producerLe_iff_probe _ _).mp h
    apply (producerLe_iff_probe _ _).mpr
    intro obs h
    exact (test (.variant label obs) ⟨rfl, h⟩).2
  · intro h
    have test := (producerLe_iff_probe _ _).mp h
    apply (producerLe_iff_probe _ _).mpr
    intro obs h
    cases obs <;> simp_all [Probe]

theorem producerLe_record_mono (label : Nat) {a b rest tail : Ty Row}
    (payload : ProducerLe leRow a b) (remaining : ProducerLe leRow rest tail) :
    ProducerLe leRow (.record label a rest) (.record label b tail) := by
  have payload := (producerLe_iff_probe _ _).mp payload
  have remaining := (producerLe_iff_probe _ _).mp remaining
  apply (producerLe_iff_probe _ _).mpr
  intro obs h
  cases obs <;> simp_all [Probe]
  case field name obs => split <;> simp_all

theorem producerLe_union_mono {a b c d : Ty Row}
    (left : ProducerLe leRow a b) (right : ProducerLe leRow c d) :
    ProducerLe leRow (.union a c) (.union b d) := by
  apply (producerLe_iff_probe _ _).mpr
  intro obs h
  exact (probe_union _ _ _).mpr
    ⟨(producerLe_iff_probe _ _).mp left obs ((probe_union _ _ _).mp h).1,
     (producerLe_iff_probe _ _).mp right obs ((probe_union _ _ _).mp h).2⟩

theorem producerLe_inter_mono {a b c d : Ty Row}
    (left : ProducerLe leRow a b) (right : ProducerLe leRow c d) :
    ProducerLe leRow (.inter a c) (.inter b d) := by
  apply (producerLe_iff_probe _ _).mpr
  intro obs h
  exact (probe_inter _ _ _).mpr (((probe_inter _ _ _).mp h).elim
    (fun h => .inl ((producerLe_iff_probe _ _).mp left obs h))
    (fun h => .inr ((producerLe_iff_probe _ _).mp right obs h)))

theorem producerLe_union_iff (a b c : Ty Row) :
    ProducerLe leRow (.union a b) c ↔ ProducerLe leRow a c ∧ ProducerLe leRow b c := by
  simp only [producerLe_iff_probe]
  constructor
  · intro h
    exact ⟨fun obs hc => ((probe_union _ _ _).mp (h obs hc)).1,
      fun obs hc => ((probe_union _ _ _).mp (h obs hc)).2⟩
  · rintro ⟨ha, hb⟩ obs hc
    exact (probe_union _ _ _).mpr ⟨ha obs hc, hb obs hc⟩

theorem producerLe_union_left (a b : Ty Row) : ProducerLe leRow a (.union a b) := by
  apply (producerLe_iff_probe _ _).mpr
  intro obs h
  exact ((probe_union _ _ _).mp h).1

theorem producerLe_union_right (a b : Ty Row) : ProducerLe leRow b (.union a b) := by
  apply (producerLe_iff_probe _ _).mpr
  intro obs h
  exact ((probe_union _ _ _).mp h).2

theorem producerEq_union_absorb {a b : Ty Row} (h : ProducerLe leRow a b) :
    ProducerEq leRow (.union a b) b :=
  ⟨(producerLe_union_iff _ _ _).mpr ⟨h, producerLe_refl _⟩, producerLe_union_right _ _⟩

/-- The current arrow boundary permits an old structural argument proof and
new producer comparison of results. No new-order argument congruence is assumed. -/
theorem producerLe_arrow (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (argument : Subtype leRow input' input) (incoming : leRow inputRow' inputRow)
    (result : ProducerLe leRow output output') (outgoing : leRow outputRow outputRow') :
    ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow') := by
  apply (producerLe_iff_probe _ _).mpr
  intro obs h
  cases obs with
  | trivial => trivial
  | arrowArgument expected => exact Subtype.trans h argument
  | arrowResult obs => exact (producerLe_iff_probe _ _).mp result obs h
  | arrowInputRow expected => exact rowTrans h incoming
  | arrowOutputRow expected => exact rowTrans outgoing h
  | impossible | base | records | pairFirst | pairLast | field | variant => exact h

@[simp] theorem accept_mask (env : Environment Row) (type : Ty Row)
    (hidden : List Nat) (demand : Demand Row) :
    Accept leRow env type (.mask hidden demand) ↔
      ∀ obs ∈ demand.observations env, Probe leRow type (obs.mask hidden) := by
  simp [Accept, Demand.observations]

/-- Same finite operations, with actual arrows and rows and legacy width `{}`;
only the producer comparison changes. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Model :=
  { StructuralBase.model Row empty join leRow with subTy := ProducerLe leRow }

end Yulang.ProducerDemand
