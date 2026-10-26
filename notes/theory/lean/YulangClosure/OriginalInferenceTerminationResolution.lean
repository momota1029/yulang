import YulangClosure.NativeValueStructure
import YulangClosure.NativeRelationInterner

/-!
Allocated-prefix chronology for the native first-empty obstruction (NQ §5.3).

This is NOT `SourceProblem.InferenceTermination`, and does not assume a finite
future allocation universe, successful drain, fairness, or a copy successor.
One history owns both row kinds, immutable term cells, real relation-interner
calls (including their failures), and exact Replay publication payloads.

The row-leaf and child-existence premises of term publication are PRODUCER
formation obligations. Rust `live_variable` does not check row availability;
we do not invent that runtime guard. Rust source-to-history extraction remains
open. Effect view interiors and rollback are outside this chronology projection.
-/
namespace YulangClosure.OriginalInferenceTerminationResolution

open NativeValuePorts (ValueEndpoint Pair Key FunctionTerms)
open NativeValueStructure (ValuePair ValueBound TermView Request)
open NativeMergeExpansion (Endpoint)

inductive Row where
  | value (id : Nat)
  | effect (id : Nat)
  deriving DecidableEq, Repr

/-- The two real ordinal supplies belong to one state and history. -/
structure Rows where
  valueLevels : List Nat := []
  effectLevels : List Nat := []

def Available (rows : Rows) : Row → Prop
  | .value id => id < rows.valueLevels.length
  | .effect id => id < rows.effectLevels.length

def Rows.Extends (a b : Rows) : Prop :=
  a.valueLevels.length ≤ b.valueLevels.length ∧
  a.effectLevels.length ≤ b.effectLevels.length

theorem available_mono {a b : Rows} (extension : a.Extends b) {row : Row}
    (present : Available a row) : Available b row := by
  cases row with
  | value => exact Nat.lt_of_lt_of_le present extension.1
  | effect => exact Nat.lt_of_lt_of_le present extension.2

def valueTerm : ValueEndpoint → Option Nat
  | .positiveFunction id | .negativeFunction id | .positiveTuple id _
  | .negativeTuple id _ | .positiveRecord id | .negativeRecord id
  | .positiveVariant id | .negativeVariant id => some id
  | _ => none

/-- Retain all four Function ports, record optionality/labels, tuple order,
and variant payloads through the existing native `TermView`. -/
inductive Cell where
  | valueLeaf (endpoint : ValueEndpoint)
  | effectLeaf (endpoint : Endpoint)
  | structure (view : TermView)
  deriving DecidableEq, Repr

def Cell.children : Cell → List Nat
  | .structure (.positiveFunction p) | .structure (.negativeFunction p) =>
      [p.argument, p.argumentEffect, p.resultEffect, p.result]
  | .structure (.positiveTuple xs) | .structure (.negativeTuple xs) => xs
  | .structure (.positiveRecord xs) | .structure (.negativeRecord xs) =>
      xs.map (fun field => field.2.ty)
  | .structure (.positiveVariant xs) | .structure (.negativeVariant xs) =>
      xs.flatMap (fun alternative => alternative.payloads)
  | _ => []

def Cell.rows : Cell → List Row
  | .valueLeaf (.row id) => [.value id]
  | .effectLeaf (.row id) => [.effect id]
  | _ => []

def Cell.readValue (id : Nat) : Cell → Option ValueEndpoint
  | .valueLeaf endpoint => some endpoint
  | .structure (.positiveFunction _) => some (.positiveFunction id)
  | .structure (.negativeFunction _) => some (.negativeFunction id)
  | .structure (.positiveTuple xs) => some (.positiveTuple id xs.length)
  | .structure (.negativeTuple xs) => some (.negativeTuple id xs.length)
  | .structure (.positiveRecord _) => some (.positiveRecord id)
  | .structure (.negativeRecord _) => some (.negativeRecord id)
  | .structure (.positiveVariant _) => some (.positiveVariant id)
  | .structure (.negativeVariant _) => some (.negativeVariant id)
  | _ => none

abbrev Cells := Nat → Option Cell

def Cells.Extends (before after : Cells) : Prop :=
  ∀ id cell, before id = some cell → after id = some cell

def Cell.Formed (rows : Rows) (cells : Cells) (cell : Cell) : Prop :=
  (∀ row ∈ cell.rows, Available rows row) ∧
  (∀ child ∈ cell.children, ∃ value, cells child = some value) ∧
  (∀ endpoint, cell = .valueLeaf endpoint → valueTerm endpoint = none)

def Cells.Formed (rows : Rows) (cells : Cells) : Prop :=
  ∀ id cell, cells id = some cell → cell.Formed rows cells

theorem cell_formed_mono {a b : Rows} {before after : Cells}
    (rowExtension : a.Extends b) (cellExtension : before.Extends after)
    {cell : Cell} (formed : cell.Formed a before) : cell.Formed b after := by
  refine ⟨fun row member => available_mono rowExtension (formed.1 row member), ?_, formed.2.2⟩
  intro child member
  obtain ⟨value, found⟩ := formed.2.1 child member
  exact ⟨value, cellExtension child value found⟩

/-- A finite syntactic path to a raw row occurrence, across BOTH kinds of
Function port. This is reference occurrence, not evaluation or subtyping. -/
inductive TermUses (cells : Cells) : Nat → Row → Prop
  | leaf {id cell row} : cells id = some cell → row ∈ cell.rows → TermUses cells id row
  | child {id cell child row} : cells id = some cell → child ∈ cell.children →
      TermUses cells child row → TermUses cells id row

theorem term_uses_available {rows : Rows} {cells : Cells}
    (formed : cells.Formed rows) {id row} (used : TermUses cells id row) :
    Available rows row := by
  induction used with
  | leaf found member => exact (formed _ _ found).1 _ member
  | child _ _ _ ih => exact ih

/-- An old immutable term cannot acquire a reference to a later row through
an old child that was previously absent: publication requires every child. -/
theorem term_uses_before {rows : Rows} {before after : Cells}
    (formed : before.Formed rows) (extension : before.Extends after)
    {id row} (used : TermUses after id row)
    (present : ∃ cell, before id = some cell) : TermUses before id row := by
  induction used with
  | leaf found member =>
      obtain ⟨old, prior⟩ := present
      have same : old = _ := Option.some.inj ((extension _ _ prior).symm.trans found)
      subst old
      exact .leaf prior member
  | child found member rest ih =>
      obtain ⟨old, prior⟩ := present
      have same : old = _ := Option.some.inj ((extension _ _ prior).symm.trans found)
      subst old
      exact .child prior member (ih ((formed _ _ prior).2.1 _ member))

def ValueAvailable (rows : Rows) (cells : Cells) (endpoint : ValueEndpoint) : Prop :=
  match endpoint with
  | .row id => Available rows (.value id)
  | endpoint => match valueTerm endpoint with
    | none => True
    | some id => ∃ cell, cells id = some cell ∧ cell.readValue id = some endpoint

def EffectAvailable (rows : Rows) : Endpoint → Prop
  | .row id => Available rows (.effect id)
  | _ => True

def PairAvailable (rows : Rows) (cells : Cells) : Pair → Prop
  | .value lower upper => ValueAvailable rows cells lower ∧ ValueAvailable rows cells upper
  | .effect lower upper => EffectAvailable rows lower ∧ EffectAvailable rows upper

theorem value_available_mono {a b : Rows} {before after : Cells}
    (rowExtension : a.Extends b) (cellExtension : before.Extends after)
    {endpoint} (available : ValueAvailable a before endpoint) :
    ValueAvailable b after endpoint := by
  cases endpoint <;> simp only [ValueAvailable, valueTerm] at available ⊢
  all_goals first
    | exact available_mono rowExtension available
    | exact trivial
    | obtain ⟨cell, found, read⟩ := available; exact ⟨cell, cellExtension _ _ found, read⟩

theorem effect_available_mono {a b : Rows} (extension : a.Extends b)
    {endpoint} (available : EffectAvailable a endpoint) : EffectAvailable b endpoint := by
  cases endpoint <;> simp only [EffectAvailable] at available ⊢
  all_goals first | exact available_mono extension available | exact trivial

theorem pair_available_mono {a b : Rows} {before after : Cells}
    (rowExtension : a.Extends b) (cellExtension : before.Extends after)
    {pair} (available : PairAvailable a before pair) : PairAvailable b after pair := by
  cases pair with
  | value => exact ⟨value_available_mono rowExtension cellExtension available.1,
      value_available_mono rowExtension cellExtension available.2⟩
  | effect => exact ⟨effect_available_mono rowExtension available.1,
      effect_available_mono rowExtension available.2⟩

inductive ValueUses (cells : Cells) : ValueEndpoint → Row → Prop
  | row (id : Nat) : ValueUses cells (.row id) (.value id)
  | term {endpoint id row} : valueTerm endpoint = some id →
      TermUses cells id row → ValueUses cells endpoint row

inductive EffectUses : Endpoint → Row → Prop
  | row (id : Nat) : EffectUses (.row id) (.effect id)

inductive PairUses (cells : Cells) : Pair → Row → Prop
  | valueLower {lower upper row} : ValueUses cells lower row → PairUses cells (.value lower upper) row
  | valueUpper {lower upper row} : ValueUses cells upper row → PairUses cells (.value lower upper) row
  | effectLower {lower upper row} : EffectUses lower row → PairUses cells (.effect lower upper) row
  | effectUpper {lower upper row} : EffectUses upper row → PairUses cells (.effect lower upper) row

theorem value_uses_prior_allocation {rows : Rows} {before after : Cells}
    (formed : before.Formed rows) (extension : before.Extends after)
    {endpoint row} (available : ValueAvailable rows before endpoint)
    (used : ValueUses after endpoint row) : Available rows row := by
  cases used with
  | row => exact available
  | @term endpoint id row pointer used =>
      have present : ∃ cell, before id = some cell := by
        cases endpoint <;> simp only [valueTerm, Option.some.injEq] at pointer
        all_goals try contradiction
        all_goals subst_vars; exact ⟨available.choose, available.choose_spec.1⟩
      exact term_uses_available formed (term_uses_before formed extension used present)

theorem pair_uses_prior_allocation {rows : Rows} {before after : Cells}
    (formed : before.Formed rows) (extension : before.Extends after)
    {pair row} (available : PairAvailable rows before pair)
    (used : PairUses after pair row) : Available rows row := by
  cases used with
  | valueLower used => exact value_uses_prior_allocation formed extension available.1 used
  | valueUpper used => exact value_uses_prior_allocation formed extension available.2 used
  | effectLower used => cases used; exact available.1
  | effectUpper used => cases used; exact available.2

/-- The actual two native bound-key kinds, without replacing an owner/endpoint
pair by a source set or a semantic equivalence class. -/
inductive Bound where
  | value (key : ValueBound)
  | effect (key : NativeMergeExpansion.Bound)
  deriving DecidableEq, Repr

def Bound.pair : Bound → Pair
  | .value bound => .value bound.pair.lower bound.pair.upper
  | .effect bound => .effect bound.pair.1 bound.pair.2

structure Admission where
  id : Nat
  key : Key
  deriving DecidableEq, Repr

/-- Raw native RelationIds AND their entire decoded keys are retained. The
decoded fields are ghost readback; context, sources, transformer and demand
are never replaced with zero/default payloads. -/
structure Replay where
  child : Admission
  lower : Admission
  upper : Admission
  lowerInput : Bound
  upperInput : Bound
  deriving DecidableEq, Repr

structure State where
  rows : Rows := {}
  cells : Cells := fun _ => none
  native : NativeRelationInterner.Native := {}
  admissions : List Admission := []
  replays : List Replay := []
  failure : Option NativeRelationInterner.Failure := none

def initial : State := {}

def State.Valid (s : State) : Prop :=
  s.cells.Formed s.rows ∧
  (∀ admission ∈ s.admissions, PairAvailable s.rows s.cells admission.key.pair) ∧
  (∀ replay ∈ s.replays,
    replay.child ∈ s.admissions ∧ replay.lower ∈ s.admissions ∧ replay.upper ∈ s.admissions ∧
    PairAvailable s.rows s.cells replay.lowerInput.pair ∧
    PairAvailable s.rows s.cells replay.upperInput.pair)

def publishCell (cells : Cells) (id : Nat) (cell : Cell) : Cells :=
  fun key => if key = id then some cell else cells key

theorem publish_extends {cells : Cells} {id : Nat} (fresh : cells id = none) (cell : Cell) :
    cells.Extends (publishCell cells id cell) := by
  intro key prior found
  by_cases same : key = id
  · subst key; rw [fresh] at found; cases found
  · simp [publishCell, same, found]

def call (s : State) (resources : NativeRelationInterner.Resources) (key : Key) : State :=
  let result := s.native.call resources key
  match result.2 with
  | .ok id => {s with native := result.1, admissions := ⟨id, key⟩ :: s.admissions}
  | .error error => {s with native := result.1, failure := some error}

/-- Each constructor is an allocation/publication cut, not a whole drain
transition. Failed real relation calls are retained; no success is postulated.
`cell`'s freshness is the term allocator's output obligation, not a new runtime
test. The native row reserve failures precede their successful append cut. -/
inductive Step : State → State → Prop
  | valueRow (s : State) (level : Nat) (running : s.failure = none)
      (ordinalFits : s.rows.valueLevels.length < 2 ^ 32) :
      Step s {s with rows := {s.rows with valueLevels := s.rows.valueLevels ++ [level]}}
  | effectRow (s : State) (level : Nat) (running : s.failure = none)
      (ordinalFits : s.rows.effectLevels.length < 2 ^ 32) :
      Step s {s with rows := {s.rows with effectLevels := s.rows.effectLevels ++ [level]}}
  | rowFailure (s : State) (running : s.failure = none) :
      Step s {s with failure := some .exhausted}
  | levels (s : State) (rows : Rows) (running : s.failure = none)
      (valueCount : rows.valueLevels.length = s.rows.valueLevels.length)
      (effectCount : rows.effectLevels.length = s.rows.effectLevels.length) :
      Step s {s with rows := rows}
  | cell (s : State) (id : Nat) (cell : Cell) (running : s.failure = none)
      (fresh : s.cells id = none) (formed : cell.Formed s.rows s.cells) :
      Step s {s with cells := publishCell s.cells id cell}
  | relation (s : State) (resources : NativeRelationInterner.Resources) (key : Key)
      (running : s.failure = none) (available : PairAvailable s.rows s.cells key.pair) :
      Step s (call s resources key)
  | inventory (s : State) (amount maximum : Nat) (running : s.failure = none)
      (fits : s.native.store.workUsed + amount ≤ maximum)
      (bounded : s.native.store.workUsed + amount ≤ 65536) :
      Step s {s with native := s.native.inventory amount}
  | replay (s : State) (entry : Replay) (running : s.failure = none)
      (child : entry.child ∈ s.admissions) (lower : entry.lower ∈ s.admissions)
      (upper : entry.upper ∈ s.admissions)
      (lowerInput : PairAvailable s.rows s.cells entry.lowerInput.pair)
      (upperInput : PairAvailable s.rows s.cells entry.upperInput.pair) :
      Step s {s with replays := entry :: s.replays}

theorem step_extension {s t : State} (step : Step s t) :
    s.rows.Extends t.rows ∧ s.cells.Extends t.cells := by
  cases step with
  | valueRow | effectRow => exact ⟨by simp [Rows.Extends], fun _ _ found => found⟩
  | rowFailure | replay | inventory => exact ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, fun _ _ found => found⟩
  | levels rows running valueCount effectCount =>
      exact ⟨⟨Nat.le_of_eq valueCount.symm, Nat.le_of_eq effectCount.symm⟩,
        fun _ _ found => found⟩
  | cell id cell running fresh formed => exact ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, publish_extends fresh _⟩
  | relation resources key =>
      cases result : (s.native.call resources key).2 <;> simp only [call, result]
      all_goals exact ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, fun _ _ found => found⟩

theorem step_valid {s t : State} (step : Step s t) (valid : s.Valid) : t.Valid := by
  obtain ⟨rowExtension, cellExtension⟩ := step_extension step
  have oldCell : ∀ id cell, s.cells id = some cell → cell.Formed t.rows t.cells :=
    fun id cell found => cell_formed_mono rowExtension cellExtension (valid.1 id cell found)
  have oldAdmission : ∀ admission ∈ s.admissions,
      PairAvailable t.rows t.cells admission.key.pair :=
    fun admission member => pair_available_mono rowExtension cellExtension (valid.2.1 admission member)
  have oldReplay : ∀ replay ∈ s.replays,
      replay.child ∈ s.admissions ∧ replay.lower ∈ s.admissions ∧ replay.upper ∈ s.admissions ∧
      PairAvailable t.rows t.cells replay.lowerInput.pair ∧
      PairAvailable t.rows t.cells replay.upperInput.pair := by
    intro replay member
    obtain ⟨child, lower, upper, li, ui⟩ := valid.2.2 replay member
    exact ⟨child, lower, upper, pair_available_mono rowExtension cellExtension li,
      pair_available_mono rowExtension cellExtension ui⟩
  cases step with
  | valueRow | effectRow | rowFailure | levels | inventory => exact ⟨oldCell, oldAdmission, oldReplay⟩
  | cell id cell running fresh formed =>
      refine ⟨?_, oldAdmission, oldReplay⟩
      intro key actual found
      by_cases same : key = id
      · subst key
        have eq : cell = actual := by simpa [publishCell] using found
        subst actual
        exact cell_formed_mono rowExtension cellExtension formed
      · exact oldCell key actual (by simpa [publishCell, same] using found)
  | relation resources key running available =>
      cases result : (s.native.call resources key).2 with
      | ok id =>
        simp only [call, result]
        refine ⟨valid.1, ?_, ?_⟩
        · intro admission member
          rcases List.mem_cons.mp member with rfl | old
          · exact available
          · exact valid.2.1 admission old
        · intro replay member
          obtain ⟨child, lower, upper, li, ui⟩ := valid.2.2 replay member
          exact ⟨List.mem_cons_of_mem _ child, List.mem_cons_of_mem _ lower,
            List.mem_cons_of_mem _ upper, li, ui⟩
      | error error => simpa only [call, result, State.Valid] using valid
  | replay entry running child lower upper li ui =>
      refine ⟨valid.1, valid.2.1, ?_⟩
      intro replay member
      rcases List.mem_cons.mp member with rfl | old
      · exact ⟨child, lower, upper, li, ui⟩
      · exact valid.2.2 replay old

inductive Run : State → State → Prop
  | nil (s : State) : Run s s
  | snoc {s t u : State} : Run s t → Step t u → Run s u

abbrev History (s : State) := Run initial s

theorem run_extension {s t : State} (run : Run s t) :
    s.rows.Extends t.rows ∧ s.cells.Extends t.cells := by
  induction run with
  | nil => exact ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, fun _ _ found => found⟩
  | snoc _ step ih =>
      obtain ⟨rows, cells⟩ := step_extension step
      exact ⟨⟨Nat.le_trans ih.1.1 rows.1, Nat.le_trans ih.1.2 rows.2⟩,
        fun id cell found => cells id cell (ih.2 id cell found)⟩

theorem history_valid {s : State} (history : History s) : s.Valid := by
  have empty : initial.Valid := by simp [State.Valid, initial, Cells.Formed]
  induction history with
  | nil => exact empty
  | snoc _ step ih => exact step_valid step ih

theorem run_trans {s t u : State} (left : Run s t) (right : Run t u) : Run s u := by
  induction right with
  | nil => exact left
  | snoc _ step ih => exact .snoc ih step

/-- An actual relation error is a terminal outcome of this projection, not
an invitation to discard the failure and continue the alleged normal run. -/
theorem failure_has_no_step {s t : State} {error : NativeRelationInterner.Failure}
    (failed : s.failure = some error) : ¬ Step s t := by
  intro step
  cases step <;> simp_all

theorem step_admissions_keep {s t : State} (step : Step s t) :
    ∀ admission ∈ s.admissions, admission ∈ t.admissions := by
  cases step with
  | valueRow | effectRow | rowFailure | levels | cell | replay | inventory => exact fun _ member => member
  | relation resources key =>
      cases result : (s.native.call resources key).2 <;> simp only [call, result]
      · exact fun _ member => List.mem_cons_of_mem _ member
      · exact fun _ member => member

theorem run_admissions_keep {s t : State} (run : Run s t) :
    ∀ admission ∈ s.admissions, admission ∈ t.admissions := by
  induction run with
  | nil => exact fun _ member => member
  | snoc _ step ih => exact fun admission member => step_admissions_keep step admission (ih admission member)

/-- The publication log is tied to the physical interner's SAME raw ID and
complete decoded Key. Its guards and partial effects on failure are reused
unchanged, including the Effect self-transformer and demand checks. -/
theorem history_native_readback {s : State} (history : History s) :
    NativeRelationInterner.NativeHistory s.native ∧
    ∀ admission ∈ s.admissions,
      s.native.store.readback admission.id = some admission.key := by
  induction history with
  | nil => exact ⟨.initial, by simp [initial]⟩
  | @snoc before after run step ih =>
      cases step with
      | valueRow | effectRow | rowFailure | levels | cell | replay => exact ih
      | inventory amount maximum running fits bounded =>
          have nr : NativeRelationInterner.NativeRun before.native
              (before.native.inventory amount) := .inventory (.nil _) amount maximum fits bounded
          refine ⟨.commit ih.1 nr, ?_⟩
          intro admission member
          have original := NativeRelationInterner.native_history_refinement ih.1
          exact NativeRelationInterner.old_relation_readback original.2
            (NativeRelationInterner.native_run_refinement nr original.1).2 (ih.2 admission member)
      | relation resources key running available =>
          have nr : NativeRelationInterner.NativeRun before.native
              (before.native.call resources key).1 := .call (.nil _) resources key
          have nh := NativeRelationInterner.NativeHistory.commit ih.1 nr
          have old : ∀ admission ∈ before.admissions,
              (before.native.call resources key).1.store.readback admission.id = some admission.key := by
            intro admission member
            have original := NativeRelationInterner.native_history_refinement ih.1
            exact NativeRelationInterner.old_relation_readback original.2
              (NativeRelationInterner.native_run_refinement nr original.1).2 (ih.2 admission member)
          cases result : (before.native.call resources key).2 with
          | ok id =>
              simp only [call, result]
              refine ⟨nh, ?_⟩
              intro admission member
              rcases List.mem_cons.mp member with rfl | member
              · exact (NativeRelationInterner.native_ok_refines_arena ih.1 result [] []).2.2.1
              · exact old admission member
          | error error =>
              simpa only [call, result] using And.intro nh old

/-- Core NQ §5.3 chronology: the exact child and both exact input BoundKeys of
an older suspended Replay cannot mention any row outside its allocated prefix,
even through a subsequently observed Function/tuple/record/variant term. -/
theorem earlier_replay_excludes_later_row {before after : State}
    (history : History before) (run : Run before after) {replay : Replay}
    (published : replay ∈ before.replays) {row : Row}
    (later : ¬ Available before.rows row) :
    ¬ PairUses after.cells replay.child.key.pair row ∧
    ¬ PairUses after.cells replay.lowerInput.pair row ∧
    ¬ PairUses after.cells replay.upperInput.pair row := by
  have valid := history_valid history
  obtain ⟨child, _, _, li, ui⟩ := valid.2.2 replay published
  have excluded : ∀ pair, PairAvailable before.rows before.cells pair →
      ¬ PairUses after.cells pair row :=
    fun _ available used => later
      (pair_uses_prior_allocation valid.1 (run_extension run).2 available used)
  exact ⟨excluded _ (valid.2.1 _ child), excluded _ li, excluded _ ui⟩

/-- The actual deduplication key contains raw RelationIds. Looking an earlier
child ID up in the later physical native store cannot turn it into a new-row
child. Thus chronology applies to native ID equality, not only ghost records. -/
theorem earlier_replay_id_excludes_later_row {before after : State}
    (history : History before) (run : Run before after) {replay : Replay}
    (published : replay ∈ before.replays) {row : Row}
    (later : ¬ Available before.rows row) {key : Key}
    (readback : after.native.store.readback replay.child.id = some key) :
    ¬ PairUses after.cells key.pair row := by
  have member := (history_valid history).2.2 replay published
  have stored := (history_native_readback (run_trans history run)).2 replay.child
    (run_admissions_keep run replay.child member.1)
  have same := NativeRelationInterner.same_id_full_key stored readback
  rw [← same]
  exact (earlier_replay_excludes_later_row history run published later).1

/-- Application to the complete native Request key: the original Context,
source set, transformer, and deferred demand travel with its raw Value pair.
No equality of a reduced diagnostic/source-set projection is used. -/
theorem earlier_replay_cannot_read_fresh_request {before after : State}
    (history : History before) (run : Run before after) {replay : Replay}
    (published : replay ∈ before.replays) {row : Row}
    (later : ¬ Available before.rows row) (request : Request)
    (occurs : ValueUses after.cells request.lower row ∨
      ValueUses after.cells request.upper row) :
    after.native.store.readback replay.child.id ≠ some request.key := by
  intro readback
  have excluded := earlier_replay_id_excludes_later_row history run published later readback
  rcases occurs with lower | upper
  · exact excluded (.valueLower lower)
  · exact excluded (.valueUpper upper)

/-- The new negative receiver appears literally in `T < N`; no source-set
or representative quotient can make this an earlier exact Replay child. -/
theorem earlier_replay_cannot_target_fresh_value {before after : State}
    (history : History before) (run : Run before after) {replay : Replay}
    (published : replay ∈ before.replays) {row : Nat}
    (fresh : before.rows.valueLevels.length ≤ row) (lower : ValueEndpoint) :
    replay.child.key.pair ≠ .value lower (.row row) := by
  intro same
  have noUse := (earlier_replay_excludes_later_row history run published
    (show ¬ Available before.rows (.value row) from Nat.not_lt_of_ge fresh)).1
  rw [same] at noUse
  exact noUse (.valueUpper (.row row))

/-- Native four-port Function readback witnesses the new argument row. The
other three ports stay in the same retained `FunctionTerms`; they are not
erased to a binary Function or required to finish. -/
theorem positive_function_uses_argument {cells : Cells} {term : Nat}
    {ports : FunctionTerms} {row : Nat}
    (function : cells term = some (.structure (.positiveFunction ports)))
    (argument : cells ports.argument = some (.valueLeaf (.row row))) :
    ValueUses cells (.positiveFunction term) (.value row) := by
  apply ValueUses.term rfl
  exact .child function (by simp [Cell.children]) (.leaf argument (by simp [Cell.rows]))

theorem earlier_replay_cannot_have_fresh_function {before after : State}
    (history : History before) (run : Run before after) {replay : Replay}
    (published : replay ∈ before.replays) {row term : Nat} {ports : FunctionTerms}
    (fresh : before.rows.valueLevels.length ≤ row)
    (function : after.cells term = some (.structure (.positiveFunction ports)))
    (argument : after.cells ports.argument = some (.valueLeaf (.row row)))
    (upper : ValueEndpoint) :
    replay.child.key.pair ≠ .value (.positiveFunction term) upper := by
  intro same
  have noUse := (earlier_replay_excludes_later_row history run published
    (show ¬ Available before.rows (.value row) from Nat.not_lt_of_ge fresh)).1
  rw [same] at noUse
  exact noUse (.valueLower (positive_function_uses_argument function argument))

end YulangClosure.OriginalInferenceTerminationResolution
