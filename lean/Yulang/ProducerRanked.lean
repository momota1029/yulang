import Yulang.ProducerDemand

/-!
# Demand-defined producer order with contextual arrow arguments

The finite rank counts nested observations of an arrow domain. At rank zero
the domain is unobserved. At a successor rank, an argument requirement is
checked with the producer order at the preceding rank. The final order
quantifies every finite rank; no rank is a solver fuel or a caller-chosen
cutoff. Rigid paths, masks and demand variables are inherited unchanged from
`ProducerDemand`.

Unlike the earlier structural-domain probe, arrow domains now use the same
demand order as all other producer positions. New-order contravariance and
congruence of arrows are proved below. The order preserves the old structural
preorder and derives same-constructor union grouping from demand observations.
This module supplies a concrete finite type model, not a constraint solver or
a model of exact/optional records and record-default images.
-/

namespace Yulang.ProducerRanked

open Inference StructuralBase
open ProducerDemand (Negative Observation Demand Environment)

universe u
variable {Row : Type u}

/-- One observational layer, parametrized only at arrow-domain comparisons. -/
def ProbeStep (leRow : Row → Row → Prop) (argumentOrder : Ty Row → Ty Row → Prop) :
    Ty Row → Observation Row → Prop
  | _, .trivial => True
  | .bottom, _ => True
  | .top, _ => False
  | .union a b, obs => ProbeStep leRow argumentOrder a obs ∧ ProbeStep leRow argumentOrder b obs
  | .inter a b, obs => ProbeStep leRow argumentOrder a obs ∨ ProbeStep leRow argumentOrder b obs
  | .base actual, .base expected => actual = expected
  | .pair a _, .pairFirst obs => ProbeStep leRow argumentOrder a obs
  | .pair _ b, .pairLast obs => ProbeStep leRow argumentOrder b obs
  | .emptyRecord, .records => True
  | .record _ _ _, .records => True
  | .record current value rest, .field label obs =>
      if label = current then ProbeStep leRow argumentOrder value obs
      else ProbeStep leRow argumentOrder rest (.field label obs)
  | .variant actual value, .variant expected obs =>
      actual = expected ∧ ProbeStep leRow argumentOrder value obs
  | .arrow input _ _ _, .arrowArgument expected => argumentOrder expected.embed input
  | .arrow _ _ output _, .arrowResult obs => ProbeStep leRow argumentOrder output obs
  | .arrow _ inputRow _ _, .arrowInputRow expected => leRow expected inputRow
  | .arrow _ _ _ outputRow, .arrowOutputRow expected => leRow outputRow expected
  | _, _ => False

/-- The rank is an observation depth for negative arrow contexts. -/
def ProbeAt (leRow : Row → Row → Prop) : Nat → Ty Row → Observation Row → Prop
  | 0 => ProbeStep leRow (fun _ _ => True)
  | rank + 1 => ProbeStep leRow (fun expected input =>
      ∀ obs, ProbeAt leRow rank input obs → ProbeAt leRow rank expected obs)

def AcceptAt (leRow : Row → Row → Prop) (rank : Nat) (env : Environment Row)
    (producer : Ty Row) (demand : Demand Row) : Prop :=
  ∀ obs ∈ demand.observations env, ProbeAt leRow rank producer obs

def ProducerLeAt (leRow : Row → Row → Prop) (rank : Nat) (source target : Ty Row) : Prop :=
  ∀ env demand, AcceptAt leRow rank env target demand → AcceptAt leRow rank env source demand

/-- Every finite negative-context rank and every union-free demand is tested. -/
def ProducerLe (leRow : Row → Row → Prop) (source target : Ty Row) : Prop :=
  ∀ rank, ProducerLeAt leRow rank source target

def ProducerEq (leRow : Row → Row → Prop) (source target : Ty Row) : Prop :=
  ProducerLe leRow source target ∧ ProducerLe leRow target source

variable {leRow : Row → Row → Prop} {argumentOrder : Ty Row → Ty Row → Prop}

@[simp] theorem probeStep_union (a b : Ty Row) (obs : Observation Row) :
    ProbeStep leRow argumentOrder (.union a b) obs ↔
      ProbeStep leRow argumentOrder a obs ∧ ProbeStep leRow argumentOrder b obs := by
  cases obs <;> simp [ProbeStep]

@[simp] theorem probeStep_inter (a b : Ty Row) (obs : Observation Row) :
    ProbeStep leRow argumentOrder (.inter a b) obs ↔
      ProbeStep leRow argumentOrder a obs ∨ ProbeStep leRow argumentOrder b obs := by
  cases obs <;> simp [ProbeStep]

@[simp] theorem probeStep_bottom (obs : Observation Row) :
    ProbeStep leRow argumentOrder (.bottom : Ty Row) obs := by
  cases obs <;> trivial

@[simp] theorem probeStep_trivial (type : Ty Row) :
    ProbeStep leRow argumentOrder type .trivial := by
  cases type <;> trivial

@[simp] theorem probeAt_union (rank : Nat) (a b : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank (.union a b) obs ↔ ProbeAt leRow rank a obs ∧ ProbeAt leRow rank b obs := by
  cases rank <;> exact probeStep_union a b obs

@[simp] theorem probeAt_inter (rank : Nat) (a b : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank (.inter a b) obs ↔ ProbeAt leRow rank a obs ∨ ProbeAt leRow rank b obs := by
  cases rank <;> exact probeStep_inter a b obs

@[simp] theorem probeAt_bottom (rank : Nat) (obs : Observation Row) :
    ProbeAt leRow rank (.bottom : Ty Row) obs := by
  cases rank <;> exact probeStep_bottom obs

@[simp] theorem probeAt_trivial (rank : Nat) (type : Ty Row) :
    ProbeAt leRow rank type .trivial := by
  cases rank <;> exact probeStep_trivial type

@[simp] theorem acceptAt_atom (rank : Nat) (env : Environment Row)
    (type : Ty Row) (obs : Observation Row) :
    AcceptAt leRow rank env type (.atom obs) ↔ ProbeAt leRow rank type obs := by
  simp [AcceptAt, Demand.observations]

@[simp] theorem acceptAt_inter (rank : Nat) (env : Environment Row)
    (type : Ty Row) (a b : Demand Row) :
    AcceptAt leRow rank env type (.inter a b) ↔
      AcceptAt leRow rank env type a ∧ AcceptAt leRow rank env type b := by
  simp [AcceptAt, Demand.observations, or_imp, forall_and]

@[simp] theorem acceptAt_mask (rank : Nat) (env : Environment Row)
    (type : Ty Row) (hidden : List Nat) (demand : Demand Row) :
    AcceptAt leRow rank env type (.mask hidden demand) ↔
      ∀ obs ∈ demand.observations env, ProbeAt leRow rank type (obs.mask hidden) := by
  simp [AcceptAt, Demand.observations]

theorem producerLeAt_iff_probe (rank : Nat) (source target : Ty Row) :
    ProducerLeAt leRow rank source target ↔
      ∀ obs, ProbeAt leRow rank target obs → ProbeAt leRow rank source obs := by
  constructor
  · intro below obs accepted
    exact (acceptAt_atom rank (fun _ => []) source obs).mp
      (below (fun _ => []) (.atom obs)
        ((acceptAt_atom rank (fun _ => []) target obs).mpr accepted))
  · intro below env demand accepted obs member
    exact below obs (accepted obs member)

theorem producerLe_iff_probe (source target : Ty Row) :
    ProducerLe leRow source target ↔
      ∀ rank obs, ProbeAt leRow rank target obs → ProbeAt leRow rank source obs := by
  exact forall_congr' fun rank => producerLeAt_iff_probe rank source target

theorem producerEq_iff_probe (source target : Ty Row) :
    ProducerEq leRow source target ↔
      ∀ rank obs, ProbeAt leRow rank source obs ↔ ProbeAt leRow rank target obs := by
  simp only [ProducerEq, producerLe_iff_probe]
  constructor
  · rintro ⟨forward, backward⟩ rank obs
    exact ⟨backward rank obs, forward rank obs⟩
  · intro same
    exact ⟨fun rank obs => (same rank obs).mpr, fun rank obs => (same rank obs).mp⟩

theorem producerLe_refl (type : Ty Row) : ProducerLe leRow type type :=
  fun _ _ _ accepted => accepted

theorem producerLe_trans {a b c : Ty Row}
    (first : ProducerLe leRow a b) (last : ProducerLe leRow b c) : ProducerLe leRow a c :=
  fun rank env demand accepted => first rank env demand (last rank env demand accepted)

theorem producerEq_refl (type : Ty Row) : ProducerEq leRow type type :=
  ⟨producerLe_refl type, producerLe_refl type⟩

theorem producerEq_symm {a b : Ty Row} (same : ProducerEq leRow a b) : ProducerEq leRow b a :=
  ⟨same.2, same.1⟩

theorem producerEq_trans {a b c : Ty Row}
    (first : ProducerEq leRow a b) (last : ProducerEq leRow b c) : ProducerEq leRow a c :=
  ⟨producerLe_trans first.1 last.1, producerLe_trans last.2 first.2⟩

private theorem probeStep_isRecord {type : Ty Row} (record : IsRecord type) :
    ProbeStep leRow argumentOrder type .records := by
  cases record <;> trivial

private theorem probeStep_record_field {type : Ty Row} (record : IsRecord type)
    (label : Nat) (obs : Observation Row) :
    ProbeStep leRow argumentOrder type (.field label obs) ↔
      ∃ value, type.lookup label = some value ∧ ProbeStep leRow argumentOrder value obs := by
  induction record with
  | empty => simp [ProbeStep, Ty.lookup]
  | @field rest current value record ih =>
      by_cases same : label = current
      · simp [ProbeStep, Ty.lookup, same]
      · simpa [ProbeStep, Ty.lookup, same] using ih

/-- The one-layer preservation lemma isolates exactly the needed property
of lower-rank domain observations. It is proved here, not an axiom. -/
private theorem probeStep_structural_preserved
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (argumentStable : ∀ {a b}, Subtype leRow a b → ∀ expected,
      argumentOrder expected a → argumentOrder expected b)
    {source target : Ty Row} (below : Subtype leRow source target) :
    ∀ obs, ProbeStep leRow argumentOrder target obs → ProbeStep leRow argumentOrder source obs := by
  induction below with
  | refl => exact fun _ accepted => accepted
  | trans _ _ first last => exact fun obs accepted => first obs (last obs accepted)
  | bottom => exact fun obs _ => probeStep_bottom obs
  | top => intro obs; cases obs <;> simp [ProbeStep]
  | unionLeft => intro obs accepted; exact ((probeStep_union _ _ obs).mp accepted).1
  | unionRight => intro obs accepted; exact ((probeStep_union _ _ obs).mp accepted).2
  | unionElim _ _ first last =>
      exact fun obs accepted => (probeStep_union _ _ obs).mpr ⟨first obs accepted, last obs accepted⟩
  | interLeft => intro obs accepted; exact (probeStep_inter _ _ obs).mpr (Or.inl accepted)
  | interRight => intro obs accepted; exact (probeStep_inter _ _ obs).mpr (Or.inr accepted)
  | interIntro _ _ first last =>
      exact fun obs accepted => ((probeStep_inter _ _ obs).mp accepted).elim (first obs) (last obs)
  | pair _ _ first last => intro obs accepted; cases obs <;> simp_all [ProbeStep]
  | variant _ payload => intro obs accepted; cases obs <;> simp_all [ProbeStep]
  | @arrow input' input inputRow' inputRow output output' outputRow outputRow'
      hi hir ho hor ihi iho =>
      intro obs accepted
      cases obs with
      | trivial => trivial
      | arrowArgument expected => exact argumentStable hi expected.embed accepted
      | arrowResult obs => exact iho obs accepted
      | arrowInputRow expected => exact rowTrans accepted hir
      | arrowOutputRow expected => exact rowTrans hor accepted
      | impossible | base | records | pairFirst | pairLast | field | variant => exact accepted
  | @record source target sourceRecord targetRecord fields subtypes ih =>
      intro obs accepted
      cases obs with
      | trivial => exact probeStep_trivial source
      | records => exact probeStep_isRecord sourceRecord
      | field label obs =>
          obtain ⟨expected, found, valid⟩ := (probeStep_record_field targetRecord label obs).mp accepted
          obtain ⟨actual, available⟩ := fields label expected found
          exact (probeStep_record_field sourceRecord label obs).mpr
            ⟨actual, available, ih label actual expected available found obs valid⟩
      | impossible | base | pairFirst | pairLast | variant | arrowArgument | arrowResult
        | arrowInputRow | arrowOutputRow => cases targetRecord <;> simp_all [ProbeStep]

/-- Every old finite structural subtype is preserved at every rank. Only
transitivity of the row order is assumed; rows and arrows are not erased. -/
theorem structural_subtype_preserved
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {source target : Ty Row} (below : Subtype leRow source target) :
    ProducerLe leRow source target := by
  apply (producerLe_iff_probe source target).mpr
  intro rank
  induction rank generalizing source target with
  | zero => exact probeStep_structural_preserved (leRow := leRow) rowTrans (fun _ _ _ => trivial) below
  | succ rank ih =>
      apply probeStep_structural_preserved (leRow := leRow) rowTrans ?_ below
      intro a b old expected accepted obs valid
      exact accepted obs (ih old obs valid)

/-- Constructor grouping holds uniformly at every negative-context rank. -/
theorem pair_union_group (a b c d : Ty Row) :
    ProducerEq leRow (.union (.pair a b) (.pair c d))
      (.pair (.union a c) (.union b d)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep]

theorem pair_union_first (a b c : Ty Row) :
    ProducerEq leRow (.pair (.union a b) c) (.union (.pair a c) (.pair b c)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep]

theorem pair_union_last (a b c : Ty Row) :
    ProducerEq leRow (.pair a (.union b c)) (.union (.pair a b) (.pair a c)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep]

theorem record_union_group (label : Nat) (a rest b tail : Ty Row) :
    ProducerEq leRow (.union (.record label a rest) (.record label b tail))
      (.record label (.union a b) (.union rest tail)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep]
  all_goals split <;> simp [*]

theorem record_union_payload (label : Nat) (a b rest : Ty Row) :
    ProducerEq leRow (.record label (.union a b) rest)
      (.union (.record label a rest) (.record label b rest)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep]
  all_goals split <;> simp [*]

theorem variant_union (label : Nat) (a b : Ty Row) :
    ProducerEq leRow (.variant label (.union a b))
      (.union (.variant label a) (.variant label b)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, and_assoc, and_left_comm]

@[simp] theorem probeAt_pairFirst (rank : Nat) (a b : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank (.pair a b) (.pairFirst obs) ↔ ProbeAt leRow rank a obs := by
  cases rank <;> rfl

@[simp] theorem probeAt_pairLast (rank : Nat) (a b : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank (.pair a b) (.pairLast obs) ↔ ProbeAt leRow rank b obs := by
  cases rank <;> rfl

@[simp] theorem probeAt_variant (rank : Nat) (actual expected : Nat)
    (payload : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank (.variant actual payload) (.variant expected obs) ↔
      actual = expected ∧ ProbeAt leRow rank payload obs := by
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
      intro rank obs accepted
      exact (probeAt_pairFirst rank a b obs).mp
        (test rank (.pairFirst obs) ((probeAt_pairFirst rank c d obs).mpr accepted))
    · apply (producerLe_iff_probe _ _).mpr
      intro rank obs accepted
      exact (probeAt_pairLast rank a b obs).mp
        (test rank (.pairLast obs) ((probeAt_pairLast rank c d obs).mpr accepted))
  · rintro ⟨first, last⟩
    have first := (producerLe_iff_probe _ _).mp first
    have last := (producerLe_iff_probe _ _).mp last
    apply (producerLe_iff_probe _ _).mpr
    intro rank obs accepted
    have first := first rank
    have last := last rank
    cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep]

theorem producerLe_variant_iff (label : Nat) (a b : Ty Row) :
    ProducerLe leRow (.variant label a) (.variant label b) ↔ ProducerLe leRow a b := by
  constructor
  · intro below
    have test := (producerLe_iff_probe _ _).mp below
    apply (producerLe_iff_probe _ _).mpr
    intro rank obs accepted
    exact ((probeAt_variant rank label label a obs).mp
      (test rank (.variant label obs) ((probeAt_variant rank label label b obs).mpr ⟨rfl, accepted⟩))).2
  · intro below
    have test := (producerLe_iff_probe _ _).mp below
    apply (producerLe_iff_probe _ _).mpr
    intro rank obs accepted
    have test := test rank
    cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep]

theorem producerLe_record_mono (label : Nat) {a b rest tail : Ty Row}
    (payload : ProducerLe leRow a b) (remaining : ProducerLe leRow rest tail) :
    ProducerLe leRow (.record label a rest) (.record label b tail) := by
  have payload := (producerLe_iff_probe _ _).mp payload
  have remaining := (producerLe_iff_probe _ _).mp remaining
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  have payload := payload rank
  have remaining := remaining rank
  cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep]
  all_goals split <;> simp_all

theorem producerLe_union_mono {a b c d : Ty Row}
    (left : ProducerLe leRow a b) (right : ProducerLe leRow c d) :
    ProducerLe leRow (.union a c) (.union b d) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  exact (probeAt_union _ _ _ _).mpr
    ⟨(producerLe_iff_probe _ _).mp left rank obs ((probeAt_union _ _ _ _).mp accepted).1,
     (producerLe_iff_probe _ _).mp right rank obs ((probeAt_union _ _ _ _).mp accepted).2⟩

theorem producerLe_inter_mono {a b c d : Ty Row}
    (left : ProducerLe leRow a b) (right : ProducerLe leRow c d) :
    ProducerLe leRow (.inter a c) (.inter b d) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  exact (probeAt_inter _ _ _ _).mpr (((probeAt_inter _ _ _ _).mp accepted).elim
    (fun valid => Or.inl ((producerLe_iff_probe _ _).mp left rank obs valid))
    (fun valid => Or.inr ((producerLe_iff_probe _ _).mp right rank obs valid)))

theorem producerLe_union_iff (a b c : Ty Row) :
    ProducerLe leRow (.union a b) c ↔ ProducerLe leRow a c ∧ ProducerLe leRow b c := by
  simp only [producerLe_iff_probe]
  constructor
  · intro below
    exact ⟨fun rank obs valid => ((probeAt_union _ _ _ _).mp (below rank obs valid)).1,
      fun rank obs valid => ((probeAt_union _ _ _ _).mp (below rank obs valid)).2⟩
  · rintro ⟨first, last⟩ rank obs valid
    exact (probeAt_union _ _ _ _).mpr ⟨first rank obs valid, last rank obs valid⟩

theorem producerLe_inter_iff (a b c : Ty Row) :
    ProducerLe leRow c (.inter a b) ↔ ProducerLe leRow c a ∧ ProducerLe leRow c b := by
  simp only [producerLe_iff_probe]
  constructor
  · intro below
    exact ⟨fun rank obs valid => below rank obs ((probeAt_inter _ _ _ _).mpr (Or.inl valid)),
      fun rank obs valid => below rank obs ((probeAt_inter _ _ _ _).mpr (Or.inr valid))⟩
  · rintro ⟨first, last⟩ rank obs valid
    exact ((probeAt_inter _ _ _ _).mp valid).elim (first rank obs) (last rank obs)

theorem producerLe_union_left (a b : Ty Row) : ProducerLe leRow a (.union a b) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  exact ((probeAt_union _ _ _ _).mp accepted).1

theorem producerLe_union_right (a b : Ty Row) : ProducerLe leRow b (.union a b) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  exact ((probeAt_union _ _ _ _).mp accepted).2

theorem producerEq_union_absorb {a b : Ty Row} (below : ProducerLe leRow a b) :
    ProducerEq leRow (.union a b) b :=
  ⟨(producerLe_union_iff _ _ _).mpr ⟨below, producerLe_refl _⟩, producerLe_union_right _ _⟩

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

/-- Arrow domains are contravariant in the new producer order itself. -/
theorem producerLe_arrow (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (argument : ProducerLe leRow input' input) (incoming : leRow inputRow' inputRow)
    (result : ProducerLe leRow output output') (outgoing : leRow outputRow outputRow') :
    ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow') := by
  have argument := (producerLe_iff_probe _ _).mp argument
  have result := (producerLe_iff_probe _ _).mp result
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  cases rank with
  | zero =>
      cases obs with
      | trivial | arrowArgument => trivial
      | arrowResult obs => exact result 0 obs accepted
      | arrowInputRow expected => exact rowTrans accepted incoming
      | arrowOutputRow expected => exact rowTrans outgoing accepted
      | impossible | base | records | pairFirst | pairLast | field | variant => exact accepted
  | succ rank =>
      cases obs with
      | trivial => trivial
      | arrowArgument expected => exact fun obs valid => accepted obs (argument rank obs valid)
      | arrowResult obs => exact result (rank + 1) obs accepted
      | arrowInputRow expected => exact rowTrans accepted incoming
      | arrowOutputRow expected => exact rowTrans outgoing accepted
      | impossible | base | records | pairFirst | pairLast | field | variant => exact accepted

theorem producerEq_arrow (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : Ty Row} (inputRow outputRow : Row)
    (argument : ProducerEq leRow input input') (result : ProducerEq leRow output output') :
    ProducerEq leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow output' outputRow) :=
  ⟨producerLe_arrow (leRow := leRow) rowTrans argument.2 (rowRefl _) result.1 (rowRefl _),
    producerLe_arrow (leRow := leRow) rowTrans argument.1 (rowRefl _) result.2 (rowRefl _)⟩

/-- Actual finite types, including arrows and effect rows, with the ranked
demand order. The inherited empty record remains the record width upper bound. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Model :=
  { StructuralBase.model Row empty join leRow with subTy := ProducerLe leRow }

namespace Examples

def rows (_ _ : Unit) : Prop := True

def diagonal : Ty Unit :=
  .union (.pair (.base .int) (.base .int)) (.pair (.base .str) (.base .str))

def grouped : Ty Unit :=
  .pair (.union (.base .int) (.base .str)) (.union (.base .int) (.base .str))

/-- Grouping remains valid even in the negative argument of an arrow. -/
theorem grouped_arrow_arguments_equal :
    ProducerEq rows (.arrow diagonal () (.base .int) ())
      (.arrow grouped () (.base .int) ()) :=
  producerEq_arrow (leRow := rows) (fun _ => trivial) (fun _ _ => trivial) () ()
    (pair_union_group _ _ _ _) (producerEq_refl _)

/-- Domain observations are substantive: the new order still distinguishes
an integer-only function from a string-only function at observation rank one. -/
theorem arrow_arguments_distinguished :
    ¬ ProducerLe rows (.arrow (.base .int) () (.base .int) ())
      (.arrow (.base .str) () (.base .int) ()) := by
  intro below
  have accepted : ProbeAt rows 1 (.arrow (.base .str) () (.base .int) ())
      (.arrowArgument (.base .str)) := fun _ valid => valid
  have domain := (producerLe_iff_probe _ _).mp below 1 (.arrowArgument (.base .str)) accepted
  have impossible := domain (.base .int) rfl
  cases impossible

end Examples

end Yulang.ProducerRanked
