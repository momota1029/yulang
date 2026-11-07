import Yulang.CommonNominalFullDemand

/-!
# Structural laws under the candidate full role-demand order

These laws are reproved against the extended observation interpreter. They
retain all nominal and float observations, expanded unknown-role head sets,
and arbitrary negative environments.
They are not inferred by pretending every new argument was an old Common type.
-/

namespace Yulang.CommonNominalFullDemand

universe u
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}
  {argumentOrder : Ty Row → Ty Row → Prop}

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
      | role | impossible | base | records | pairFirst | pairLast | field | optional | variant |
          float | nominalHead | nominalLower | nominalUpper | nominalRowLower | nominalRowUpper => exact accepted
  | succ rank =>
      cases obs with
      | trivial => trivial
      | arrowArgument expected =>
          exact fun next obs valid => accepted next obs (argument rank next obs valid)
      | arrowResult obs => exact result (rank + 1) env obs accepted
      | arrowInputRow expected => exact rowTrans accepted incoming
      | arrowOutputRow expected => exact rowTrans outgoing accepted
      | role | impossible | base | records | pairFirst | pairLast | field | optional | variant |
          float | nominalHead | nominalLower | nominalUpper | nominalRowLower | nominalRowUpper => exact accepted

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


end Yulang.CommonNominalFullDemand
