import YulangClosure.Contracts
import YulangClosure.NativeFreshScopeTransport

/-!
NATIVE-FRESH-BOUND-ADMISSION/r2. Constructed, NOT_CHECKED before phase-1 review.

Successful-operation projection of candidate_scheme.rs:4669--4715,
candidate_effect.rs:714--777, candidate_context.rs:775--839,3888--3937,
4259--4276 and candidate_extrusion.rs:648--875,966--1033 at the contract pins.
No source typing, full FreshUse coverage, replay termination, temporal prepared
root preservation, or executable Rust refinement is asserted.

The ordinary parent/context cut is explicit: `ordinaryParent` is the parent
selected by candidate_context_bound_for, and `ordinaryContext` is its computed
post-check context (or checked-boundary identity). This module does not prove
that upstream parent selection or the semantic check is correct. It computes
the ordinary child key and interning below that cut; it does not take the
admitted child, attachment, physical slot, or emission as an input.

Bound endpoints are canonical at insertion. Atom numbers retain opaque native
endpoint identity; no endpoint semantics is inferred. Eight lanes remain
separate. Tables model successful vector operations; allocation failure,
HashMap implementation, resource accounting, coverage bits, origin sets,
journals, and other interleaved mutations are outside this local projection.
-/
namespace YulangClosure.NativeFreshBoundAdmissionR2

open NativeScopeTransformer

/-- Zero-based vector lookup, without identifying any two equal occurrences. -/
def at {α : Type} : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => at rest index

theorem at_append_new {α : Type} (rows : List α) (value : α) :
    at (rows ++ [value]) rows.length = some value := by
  induction rows with
  | nil => rfl
  | cons head rest ih => simpa only [List.cons_append, List.length_cons, at] using ih

/-- The successful key interner, including both existing-key and new-row cases.
Native key uniqueness makes its first matching slot the HashMap's slot. -/
def intern {α : Type} [DecidableEq α] (key : α) : List α → Nat × List α
  | [] => (0, [key])
  | head :: rest =>
      if head = key then (0, head :: rest)
      else let result := intern key rest
           (result.1 + 1, head :: result.2)

theorem intern_read {α : Type} [DecidableEq α] (key : α) (rows : List α) :
    at (intern key rows).2 (intern key rows).1 = some key := by
  induction rows with
  | nil => rfl
  | cons head rest ih =>
      by_cases same : head = key
      · simp [intern, same, at]
      · simpa only [intern, same, ↓reduceIte, at] using ih

inductive Kind where | value | effect
  deriving DecidableEq, Repr
inductive Side where | positive | negative
  deriving DecidableEq, Repr
inductive Item where | row (id : Nat) | atom (id : Nat)
  deriving DecidableEq, Repr

structure Bound where
  kind : Kind
  owner : Nat
  side : Side
  item : Item
  deriving DecidableEq, Repr

structure Pair where
  kind : Kind
  lower : Item
  upper : Item
  deriving DecidableEq, Repr

def Bound.pair (bound : Bound) : Pair :=
  match bound.side with
  | .positive => ⟨bound.kind, bound.item, .row bound.owner⟩
  | .negative => ⟨bound.kind, .row bound.owner, bound.item⟩

/-- Kind/side/item tag is the exact eight-way lane dispatch. -/
structure Lane where
  kind : Kind
  side : Side
  rowItem : Bool
  deriving DecidableEq, Repr

def Bound.lane (bound : Bound) : Lane :=
  ⟨bound.kind, bound.side, match bound.item with | .row _ => true | .atom _ => false⟩

structure Slot where
  owner : Nat
  lane : Lane
  index : Nat
  deriving DecidableEq, Repr

abbrev Physical := Nat → Lane → List Item

def readPhysical (rows : Physical) (slot : Slot) : Option Bound :=
  (at (rows slot.owner slot.lane) slot.index).map fun item =>
    ⟨slot.lane.kind, slot.owner, slot.lane.side, item⟩

def appendPhysical (rows : Physical) (bound : Bound) : Slot × Physical :=
  (⟨bound.owner, bound.lane, (rows bound.owner bound.lane).length⟩,
    fun owner lane => if owner = bound.owner ∧ lane = bound.lane
      then rows owner lane ++ [bound.item] else rows owner lane)

theorem append_physical_read (rows : Physical) (bound : Bound) :
    readPhysical (appendPhysical rows bound).2 (appendPhysical rows bound).1 = some bound := by
  cases bound with
  | mk kind owner side item =>
      simp [readPhysical, appendPhysical, Bound.lane, at_append_new]

/-- All five demand coordinates are retained as opaque IDs, including root. -/
structure Demand where
  originalCall : Nat
  useInstance : Nat
  root : Nat
  outputScope : Nat
  input : Nat
  deriving DecidableEq, Repr

structure Flow where
  transformer : Nat := 0
  demand : Option Demand := none
  deriving DecidableEq, Repr

structure RelationKey where
  pair : Pair
  context : Nat
  sources : Option Nat
  scoped : Nat
  deriving DecidableEq, Repr

structure Snapshot where
  sourceBound : Bound
  relation : Option Nat
  deriving DecidableEq, Repr

structure Transport where
  child : Nat
  parent : Nat
  useOrigin : Nat
  sourceBound : Bound
  targetBound : Bound
  deriving DecidableEq, Repr

structure Inventory where
  relations : List RelationKey
  flows : List Flow
  transformers : List Transformer
  snapshots : List Snapshot
  transports : List Transport

/-- Flow zero is a default value, while physical flow slots are zero-based. -/
def flowAt (inventory : Inventory) : Nat → Option Flow
  | 0 => some ⟨0, none⟩
  | index + 1 => at inventory.flows index

/-- Transformer identity is logical. Physical raw slot zero means root one. -/
def physicalRaw (inventory : Inventory) : Nat → Option Transformer
  | 0 => none
  | index + 1 => at inventory.transformers index

def rawAt (inventory : Inventory) : Nat → Option Transformer
  | 0 => some ⟨[], []⟩
  | index + 1 => at inventory.transformers index

theorem identity_has_no_physical_slot (inventory : Inventory) :
    physicalRaw inventory 0 = none := rfl

def relationRaw (inventory : Inventory) (relation : Nat) : Option (Nat × Transformer) := do
  let key ← at inventory.relations relation
  let flow ← flowAt inventory key.scoped
  let raw ← rawAt inventory flow.transformer
  pure (flow.transformer, raw)

/-- Ordinal belongs to this invocation, not to an endpoint-set key or admission.
The native FreshUse cause itself contains the other four source fields. -/
structure Call where
  ordinal : Nat
  sourceBound : Bound
  antecedent : Nat
  useOrigin : Nat
  mapped : Option Nat
  target : Bound
  deriving DecidableEq, Repr

structure Cause where
  antecedent : Nat
  useOrigin : Nat
  sourceBound : Bound
  mapped : Option Nat
  deriving DecidableEq, Repr

def Call.cause (call : Call) : Cause :=
  ⟨call.antecedent, call.useOrigin, call.sourceBound, call.mapped⟩

/-- The successful scoped reuse checks the actual snapshot, target pair,
nonzero use, and retained FreshUse transport, before returning the mapped ID. -/
def scopedAdmission (inventory : Inventory) (call : Call) : Option (Nat × Inventory) := do
  let relation ← call.mapped
  let snapshot ← at inventory.snapshots call.antecedent
  let parent ← snapshot.relation
  let key ← at inventory.relations relation
  if snapshot.sourceBound = call.sourceBound ∧ key.pair = call.target.pair ∧
      call.useOrigin ≠ 0 ∧
      Transport.mk relation parent call.useOrigin call.sourceBound call.target ∈ inventory.transports
  then pure (relation, inventory) else none

/-- Ordinary bound payload, including Value/Effect incompatibility checks.
The returned scope-flow ID already names either the parent's flow or default. -/
def ordinaryFlow (inventory : Inventory) (parent : RelationKey) (target : Pair) : Option Nat := do
  let flow ← flowAt inventory parent.scoped
  if (parent.pair.kind = .value ∧ flow.transformer ≠ 0) ∨
      (parent.pair.kind = .effect ∧ flow.demand ≠ none) then none
  else if flow = (⟨0, none⟩ : Flow) then pure 0
  else if parent.pair.kind = target.kind then pure parent.scoped
  else if parent.pair.kind = .value then pure 0 else none

/-- Below candidate_context_bound_for's resolved parent/context cut. Unscoped
admission computes and interns its ordinary key independently of `call.mapped`.
No desired child attachment or admitted relation is supplied to this function. -/
def unscopedAdmission (inventory : Inventory) (call : Call)
    (ordinaryParent ordinaryContext : Nat) : Option (Nat × Inventory) := do
  let parent ← at inventory.relations ordinaryParent
  let scoped ← ordinaryFlow inventory parent call.target.pair
  let childFlow ← flowAt inventory scoped
  if childFlow.transformer ≠ 0 ∧ call.target.pair.kind = .effect ∧
      call.target.pair.lower = call.target.pair.upper then none
  else
    let key : RelationKey := ⟨call.target.pair, ordinaryContext, parent.sources, scoped⟩
    let result := intern key inventory.relations
    pure (result.1, { inventory with relations := result.2 })

inductive Mode where
  | scoped
  | unscoped (ordinaryParent ordinaryContext : Nat)
  deriving DecidableEq, Repr

def admitRelation (mode : Mode) (inventory : Inventory) (call : Call) :=
  match mode with
  | .scoped => scopedAdmission inventory call
  | .unscoped parent context => unscopedAdmission inventory call parent context

structure Admission where
  bound : Bound
  relation : Nat
  cause : Cause
  deriving DecidableEq, Repr

structure Readback where
  slot : Slot
  bound : Bound
  deriving DecidableEq, Repr

structure Emission where
  admission : Nat
  bound : Bound
  physical : Slot
  readback : Readback
  deriving DecidableEq, Repr

structure State where
  inventory : Inventory
  admissions : List Admission
  emissions : List Emission
  physical : Physical

structure Inserted where
  state : State
  returnedEmission : Nat

/-- candidate_insert_bound_with_evidence: admission index, physical append,
actual addressed read, equality check, then evidence_emit. The desired raw
transformer is never inserted here. Inventory changes only through admission. -/
def insert (mode : Mode) (before : State) (call : Call) : Option Inserted := do
  let (relation, inventory) ← admitRelation mode before.inventory call
  let admission : Admission := ⟨call.target, relation, call.cause⟩
  let physical := appendPhysical before.physical call.target
  let actual ← readPhysical physical.2 physical.1
  if actual = call.target then
    let emission : Emission := ⟨before.admissions.length, call.target,
      physical.1, ⟨physical.1, actual⟩⟩
    pure ⟨⟨inventory, before.admissions ++ [admission],
      before.emissions ++ [emission], physical.2⟩, before.emissions.length⟩
  else none

/-- No assumption about desired attachments: this is the reduced insert result
for an actually successful relation-admission branch. -/
theorem insert_of_admission (mode : Mode) (before : State) (call : Call)
    (relation : Nat) (inventory : Inventory)
    (admitted : admitRelation mode before.inventory call = some (relation, inventory)) :
    insert mode before call = some
      ⟨⟨inventory, before.admissions ++ [⟨call.target, relation, call.cause⟩],
        before.emissions ++ [⟨before.admissions.length, call.target,
          (appendPhysical before.physical call.target).1,
          ⟨(appendPhysical before.physical call.target).1, call.target⟩⟩],
        (appendPhysical before.physical call.target).2⟩, before.emissions.length⟩ := by
  simp [insert, admitted, append_physical_read]

/-- Saved restoration owner. Each intermediate constructor stands for one
successfully completed child/replay; it does not assert those children succeed.
The final n=count branch returns the saved insertion emission unchanged. -/
inductive DriverReturns (savedEmission : Nat) : Nat → Nat → Nat → Prop where
  | done (count : Nat) : DriverReturns savedEmission count count savedEmission
  | child {next count returned : Nat} :
      DriverReturns savedEmission (next + 1) count returned →
      DriverReturns savedEmission next count returned

theorem driver_returns_saved {saved next count returned : Nat}
    (completed : DriverReturns saved next count returned) : returned = saved := by
  induction completed with
  | done => rfl
  | child _ ih => exact ih

/-- The join follows the DRIVER-returned emission, its admission index and its
addressed physical slot. Ordinal stays with the initiating invocation. -/
def Corresponds (after : State) (call : Call) (returned admittedRelation : Nat) : Prop :=
  ∃ emission : Emission, ∃ admission : Admission,
    at after.emissions returned = some emission ∧
    at after.admissions emission.admission = some admission ∧
    emission.bound = call.target ∧ admission.bound = call.target ∧
    admission.relation = admittedRelation ∧ admission.cause = call.cause ∧
    readPhysical after.physical emission.physical = some call.target ∧
    emission.readback.slot = emission.physical ∧ emission.readback.bound = call.target

/-- Local conditional mathematics only. In particular, it supplies neither
scopedAdmission's transport premises nor a concrete original source witness. -/
theorem same_bound_from_returned_emission (mode : Mode) (before : State) (call : Call)
    (relation : Nat) (inventory : Inventory)
    (admitted : admitRelation mode before.inventory call = some (relation, inventory))
    (after : Inserted) (inserted : insert mode before call = some after)
    (next count returned : Nat)
    (completed : DriverReturns after.returnedEmission next count returned) :
    Corresponds after.state call returned relation ∧
      relationRaw after.state.inventory relation = relationRaw inventory relation := by
  have reduced := insert_of_admission mode before call relation inventory admitted
  rw [reduced] at inserted
  cases inserted
  have returnedSame := driver_returns_saved completed
  subst returned
  constructor
  · exact ⟨_, _, at_append_new _ _, at_append_new _ _, rfl, rfl, rfl, rfl,
      append_physical_read _ _, rfl, rfl⟩
  · rfl

/-- Raw content is read through the actual admitted relation's physical row,
its scoped-flow slot and its root. It is not sampled through the mapped ID. -/
theorem admitted_raw_readback (inventory : Inventory) (relation : Nat)
    (key : RelationKey) (flow : Flow) (raw : Transformer)
    (row : at inventory.relations relation = some key)
    (flowRow : flowAt inventory key.scoped = some flow)
    (rawRow : rawAt inventory flow.transformer = some raw) :
    relationRaw inventory relation = some (flow.transformer, raw) := by
  simp [relationRaw, row, flowRow, rawRow]

structure Observed where
  cause : Cause
  bound : Bound
  admittedRelation : Nat
  physical : Slot
  root : Nat
  raw : Transformer

/-- Completion may have changed effective roots. Read the CURRENT inventory
through the saved emission's admission; never substitute a prepared root. -/
def observeCompleted (state : State) (returned : Nat) : Option Observed := do
  let emission ← at state.emissions returned
  let admission ← at state.admissions emission.admission
  let (root, raw) ← relationRaw state.inventory admission.relation
  pure ⟨admission.cause, emission.bound, admission.relation, emission.physical, root, raw⟩

/-- Current root/raw are unrestricted. Evidence rows remain those reached by
this invocation's returned emission. This establishes association, not temporal
prepared-root equality or stability across an arbitrary native history. -/
theorem completed_raw_readback (after : State) (call : Call) (returned relation : Nat)
    (current : Inventory) (root : Nat) (raw : Transformer)
    (joined : Corresponds after call returned relation)
    (read : relationRaw current relation = some (root, raw)) :
    ∃ slot, observeCompleted { after with inventory := current } returned =
      some ⟨call.cause, call.target, relation, slot, root, raw⟩ := by
  obtain ⟨emission, admission, er, ar, eb, _, relationSame, causeSame, _, _, _⟩ := joined
  refine ⟨emission.physical, ?_⟩
  simp [observeCompleted, er, ar, relationSame, causeSame, eb, read]

/-- Every invocation emits a new row even when bound/cause/relation coincide.
Native evidence_admit also appends on duplicate origin_keys. -/
theorem duplicate_occurrences_get_distinct_emissions (mode₁ mode₂ : Mode)
    (before : State) (first second : Call) (one two : Inserted)
    (relation₁ relation₂ : Nat) (inventory₁ inventory₂ : Inventory)
    (a₁ : admitRelation mode₁ before.inventory first = some (relation₁, inventory₁))
    (i₁ : insert mode₁ before first = some one)
    (a₂ : admitRelation mode₂ one.state.inventory second = some (relation₂, inventory₂))
    (i₂ : insert mode₂ one.state second = some two) :
    one.returnedEmission ≠ two.returnedEmission := by
  have r₁ := insert_of_admission mode₁ before first relation₁ inventory₁ a₁
  rw [r₁] at i₁
  cases i₁
  have r₂ := insert_of_admission mode₂ _ second relation₂ inventory₂ a₂
  rw [r₂] at i₂
  cases i₂
  simp

/-- Scoped success returns precisely the mapped ID, with no new relation row.
This follows the checks; it is not an assumption of ID equality. -/
theorem scoped_admission_reuses (inventory : Inventory) (call : Call)
    (relation : Nat) (snapshot : Snapshot) (parent : Nat) (key : RelationKey)
    (mapped : call.mapped = some relation)
    (snapshotRow : at inventory.snapshots call.antecedent = some snapshot)
    (parentRow : snapshot.relation = some parent)
    (relationRow : at inventory.relations relation = some key)
    (source : snapshot.sourceBound = call.sourceBound)
    (pair : key.pair = call.target.pair) (nonzero : call.useOrigin ≠ 0)
    (transport : Transport.mk relation parent call.useOrigin call.sourceBound call.target ∈
      inventory.transports) :
    admitRelation .scoped inventory call = some (relation, inventory) := by
  simp [admitRelation, scopedAdmission, mapped, snapshotRow, parentRow,
    relationRow, source, pair, nonzero, transport]

/-- The interner supplies the ordinary relation row from its calculated key;
there is no equality premise between that result and the mapped child. -/
theorem unscoped_calculated_row (inventory : Inventory) (call : Call)
    (parentId context : Nat) (parent : RelationKey) (scoped : Nat) (childFlow : Flow)
    (parentRow : at inventory.relations parentId = some parent)
    (flow : ordinaryFlow inventory parent call.target.pair = some scoped)
    (childFlowRow : flowAt inventory scoped = some childFlow)
    (insertable : ¬ (childFlow.transformer ≠ 0 ∧ call.target.pair.kind = .effect ∧
      call.target.pair.lower = call.target.pair.upper)) :
    let key : RelationKey := ⟨call.target.pair, context, parent.sources, scoped⟩
    let result := intern key inventory.relations
    admitRelation (.unscoped parentId context) inventory call =
      some (result.1, { inventory with relations := result.2 }) ∧
    at result.2 result.1 = some key := by
  constructor
  · simp [admitRelation, unscopedAdmission, parentRow, flow, childFlowRow, insertable]
  · exact intern_read _ _

/-- Source-review examples are reductions of this model, not native receipts. -/
def exampleSource : Bound := ⟨.effect, 1, .positive, .row 0⟩
def exampleTarget : Bound := ⟨.effect, 4, .positive, .row 3⟩
def exampleCall : Call := ⟨9, exampleSource, 0, 2, some 1, exampleTarget⟩
def exampleInventory (scoped : Nat) : Inventory :=
  ⟨[⟨exampleSource.pair, 0, none, scoped⟩,
    ⟨exampleTarget.pair, 7, none, scoped⟩],
   [⟨1, none⟩], [NativeScopeTransformer.release 0],
   [⟨exampleSource, some 0⟩],
   [⟨1, 0, 2, exampleSource, exampleTarget⟩]⟩

theorem scoped_nonidentity_branch :
    admitRelation .scoped (exampleInventory 1) exampleCall =
      some (1, exampleInventory 1) ∧
    relationRaw (exampleInventory 1) 1 = some (1, NativeScopeTransformer.release 0) := by
  constructor <;> rfl

theorem unscoped_mapped_admitted_differ :
    let before := exampleInventory 0
    let key : RelationKey := ⟨exampleTarget.pair, 0, none, 0⟩
    let after := { before with relations := before.relations ++ [key] }
    admitRelation (.unscoped 0 0) before exampleCall = some (2, after) ∧
    exampleCall.mapped = some 1 ∧ (1 : Nat) ≠ 2 ∧
    relationRaw after 2 = some (0, ⟨[], []⟩) ∧ physicalRaw after 0 = none := by
  constructor
  · rfl
  · exact ⟨rfl, by decide, rfl, rfl⟩

end YulangClosure.NativeFreshBoundAdmissionR2

