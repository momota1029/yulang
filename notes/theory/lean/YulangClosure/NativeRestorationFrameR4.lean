import YulangClosure.Contracts
import YulangClosure.NativeScopeTransformer

/-!
NATIVE-RESTORATION-FRAME/r4, candidate local projection algebra.

This file is CONSTRUCTED, UNCHECKED. The packet requires source-first review
before the primary's single bounded Lean check. The declarations below must
not be reported as kernel accepted until their printed types and axioms exist.

Source pins are those in contract SHA256
0c76993f4759bef5ff466fd039ce5d551fcec10996ab6d6c40f6643a5af87902.
The represented writes are inventoried in the one leased proof handoff.
`Write` is a projection of enumerated local writes, not an established
simulation of every Rust child. In particular `ModelDriverReturns` is NOT
identified with successful native execution. The open source-to-sequence
bridge is neither a preservation field nor a completed-lookup assumption.

The original SourceProblem.InferenceSoundness, source domain, shared witness,
prepared-root temporal theorem and every FreshUse route remain OPEN.
-/
namespace YulangClosure.NativeRestorationFrameR4

open NativeScopeTransformer (Transformer)

/-- Term and view handles remain opaque native identities. -/
inductive ValueEndpoint where
  | bottomPositive | bottomNegative | topNegative
  | intPositive | intNegative | unitPositive | boolPositive | strPositive
  | unitNegative | boolNegative | strNegative
  | row (id : Nat)
  | positiveFunction (term : Nat) | negativeFunction (term : Nat)
  | positiveVariant (term : Nat) | negativeVariant (term : Nat)
  | positiveRecord (term : Nat) | negativeRecord (term : Nat)
  | positiveTuple (term count : Nat) | negativeTuple (term count : Nat)
  deriving DecidableEq

inductive EffectEndpoint where
  | bottomPositive | emptyNegative
  | contribution (id : Nat) | allowance (id : Nat) | support (id : Nat)
  | annotationMember (view member : Nat) | row (id : Nat)
  deriving DecidableEq

inductive Endpoint where
  | value (endpoint : ValueEndpoint)
  | effect (endpoint : EffectEndpoint)
  deriving DecidableEq

inductive RowKey where
  | value (id : Nat) | effect (id : Nat)
  deriving DecidableEq

inductive Polarity where
  | positive | negative
  deriving DecidableEq

inductive Lane where
  | valueLowerRow | valueUpperRow | valueLowerAtom | valueUpperAtom
  | effectLowerRow | effectUpperRow | effectLowerAtom | effectUpperAtom
  deriving DecidableEq

def rowEndpoint : RowKey → Endpoint
  | .value id => .value (.row id)
  | .effect id => .effect (.row id)

def laneSide : Lane → Polarity
  | .valueLowerRow | .valueLowerAtom | .effectLowerRow | .effectLowerAtom => .positive
  | .valueUpperRow | .valueUpperAtom | .effectUpperRow | .effectUpperAtom => .negative

/-- Every RowKey × Lane combination is represented; crossed kinds reject. -/
def laneFits : RowKey → Lane → Bool
  | .value _, .valueLowerRow | .value _, .valueUpperRow
  | .value _, .valueLowerAtom | .value _, .valueUpperAtom => true
  | .effect _, .effectLowerRow | .effect _, .effectUpperRow
  | .effect _, .effectLowerAtom | .effect _, .effectUpperAtom => true
  | _, _ => false

/-- The exact lane chosen by the eight insert_bound! successful cases. -/
def insertionLane : RowKey → Polarity → Endpoint → Option Lane
  | .value _, .positive, .value (.row _) => some .valueLowerRow
  | .value _, .negative, .value (.row _) => some .valueUpperRow
  | .value _, .positive, .value _ => some .valueLowerAtom
  | .value _, .negative, .value _ => some .valueUpperAtom
  | .effect _, .positive, .effect (.row _) => some .effectLowerRow
  | .effect _, .negative, .effect (.row _) => some .effectUpperRow
  | .effect _, .positive, .effect _ => some .effectLowerAtom
  | .effect _, .negative, .effect _ => some .effectUpperAtom
  | _, _, _ => none

structure BoundKey where
  owner : Endpoint
  side : Polarity
  item : Endpoint
  deriving DecidableEq

inductive Pair where
  | value (lower upper : ValueEndpoint)
  | effect (lower upper : EffectEndpoint)
  deriving DecidableEq

inductive TransportReason where
  | extrusion (operation : Endpoint) (polarity : Polarity) (target : Nat)
  | parentCopy (parentIndex : Nat)
  | equalityCanonicalization | freshUse
  deriving DecidableEq

inductive AdmissionCause where
  | ownerEmission (processing : Option Nat)
  | extrusionLink (processing : Option Nat)
  | freshUse (antecedent useOrigin : Nat) (sourceBound : BoundKey)
      (mappedRelation : Option Nat)
  | boundTransport (antecedent : Nat) (reason : TransportReason)
  deriving DecidableEq

structure Slot where
  owner : RowKey
  lane : Lane
  index : Nat
  deriving DecidableEq

structure Admission where
  bound : BoundKey
  origin : Pair
  relation : Option Nat
  cause : AdmissionCause
  coverage : Nat
  group : Nat
  previousOnGroup : Option Nat

structure Emission where
  admission : Nat
  bound : BoundKey
  physical : Slot
  readbackSlot : Slot
  readbackBound : BoundKey
  previousOnGroup : Option Nat

structure Relation where
  pair : Pair
  context : Nat
  sources : Option Nat
  scoped : Nat
  previousOnPair : Option Nat

/-- The complete native ScopedDemand is retained as an opaque parameter. -/
structure Flow (Demand : Type) where
  transformer : Nat
  demand : Option Demand

/-- Zero-based vector lookup, defined here to keep its append proof local. -/
def at {α : Type} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => at tail index

theorem at_append_of_some {α : Type} (before suffix : List α) (index : Nat) (value : α)
    (found : at before index = some value) :
    at (before ++ suffix) index = some value := by
  induction before generalizing index with
  | nil => simp [at] at found
  | cons head tail ih =>
      cases index with
      | zero => simpa only [List.cons_append, at] using found
      | succ index =>
          simp only [List.cons_append, at] at found ⊢
          exact ih index found

theorem at_append_end {α : Type} (before : List α) (value : α) :
    at (before ++ [value]) before.length = some value := by
  induction before with
  | nil => rfl
  | cons head tail ih => simpa only [List.cons_append, List.length_cons, at] using ih

/-- The projected physical vectors contain uncanonicalized stored endpoints.
An absent native owner/lane projects to []; allocating an empty row therefore
does not change this projection. Native owner existence is still an input to
the source-to-projection bridge, not inferred from this total function. -/
structure State (Demand : Type) where
  admissions : List Admission
  emissions : List Emission
  relations : List Relation
  flows : List (Flow Demand)
  transformers : List Transformer
  physical : RowKey → Lane → List Endpoint
  forest : RowKey → RowKey

def physicalAt (state : State Demand) (slot : Slot) : Option Endpoint :=
  at (state.physical slot.owner slot.lane) slot.index

def physicalKey (state : State Demand) (slot : Slot) : Option BoundKey :=
  if laneFits slot.owner slot.lane then
    (physicalAt state slot).map fun item => ⟨rowEndpoint slot.owner, laneSide slot.lane, item⟩
  else none

/-- Logical identity does not occupy physical transformer row zero. -/
def rawTransformer (state : State Demand) : Nat → Option Transformer
  | 0 => some NativeScopeTransformer.identity
  | index + 1 => at state.transformers index

def scopedFlow (state : State Demand) : Nat → Option (Flow Demand)
  | 0 => some ⟨0, none⟩
  | index + 1 => at state.flows index

def appendPhysical (state : State Demand) (owner : RowKey) (lane : Lane)
    (item : Endpoint) : State Demand :=
  { state with physical := fun key side =>
      if key = owner ∧ side = lane then state.physical key side ++ [item]
      else state.physical key side }

theorem appendPhysical_old (state : State Demand) (owner : RowKey) (lane : Lane)
    (item : Endpoint) (slot : Slot) (old : Endpoint)
    (found : physicalAt state slot = some old) :
    physicalAt (appendPhysical state owner lane item) slot = some old := by
  unfold physicalAt appendPhysical
  split
  · exact at_append_of_some _ _ _ _ found
  · exact found

theorem appendPhysical_new (state : State Demand) (owner : RowKey) (lane : Lane)
    (item : Endpoint) :
    physicalAt (appendPhysical state owner lane item)
      ⟨owner, lane, (state.physical owner lane).length⟩ = some item := by
  unfold physicalAt appendPhysical
  rw [if_pos ⟨rfl, rfl⟩]
  exact at_append_end _ _

/-- Only existing addressed records are framed. Representatives may change. -/
structure Frame (before after : State Demand) : Prop where
  admissions : ∀ index value, at before.admissions index = some value →
    at after.admissions index = some value
  emissions : ∀ index value, at before.emissions index = some value →
    at after.emissions index = some value
  relations : ∀ index value, at before.relations index = some value →
    at after.relations index = some value
  flows : ∀ index value, at before.flows index = some value →
    at after.flows index = some value
  transformers : ∀ index value, at before.transformers index = some value →
    at after.transformers index = some value
  physical : ∀ slot value, physicalAt before slot = some value →
    physicalAt after slot = some value

theorem Frame.refl (state : State Demand) : Frame state state :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
   fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem Frame.trans {first middle last : State Demand}
    (left : Frame first middle) (right : Frame middle last) : Frame first last :=
  ⟨fun i v h => right.admissions i v (left.admissions i v h),
   fun i v h => right.emissions i v (left.emissions i v h),
   fun i v h => right.relations i v (left.relations i v h),
   fun i v h => right.flows i v (left.flows i v h),
   fun i v h => right.transformers i v (left.transformers i v h),
   fun s v h => right.physical s v (left.physical s v h)⟩

theorem Frame.physical_key {before after : State Demand} (frame : Frame before after)
    (slot : Slot) (key : BoundKey) (found : physicalKey before slot = some key) :
    physicalKey after slot = some key := by
  unfold physicalKey at found ⊢
  split at found
  · rename_i fits
    rw [if_pos fits]
    cases value : physicalAt before slot with
    | none =>
        rw [value] at found
        cases found
    | some item =>
        rw [value] at found
        rw [frame.physical slot item value]
        exact found
  · cases found

theorem Frame.raw_transformer {before after : State Demand} (frame : Frame before after)
    (index : Nat) (value : Transformer) (found : rawTransformer before index = some value) :
    rawTransformer after index = some value := by
  cases index with
  | zero => exact found
  | succ index => exact frame.transformers index value found

theorem Frame.scoped_flow {before after : State Demand} (frame : Frame before after)
    (index : Nat) (value : Flow Demand) (found : scopedFlow before index = some value) :
    scopedFlow after index = some value := by
  cases index with
  | zero => exact found
  | succ index => exact frame.flows index value found

/-! These are local successful WRITE footprints. Conditions authenticate only
the stated local branch; allocation/call/finite-word/source simulation is open.
No constructor accepts a frame proof or a completed-lookup proposition. -/
inductive Write : State Demand → State Demand → Prop
  /-- candidate_context::EvidenceStore::admit, both duplicate branches. -/
  | admission (state : State Demand) (record : Admission) :
      Write state { state with admissions := state.admissions ++ [record] }
  /-- EvidenceStore::emit, after reserve and successful physical readback. -/
  | emission (state : State Demand) (record : Emission)
      (admission : Admission)
      (admitted : at state.admissions record.admission = some admission)
      (same : record.bound = admission.bound)
      (slot : record.readbackSlot = record.physical)
      (readback : physicalKey state record.physical = some record.readbackBound)
      (bound : record.readbackBound = record.bound) :
      Write state { state with emissions := state.emissions ++ [record] }
  /-- candidate_extrusion insert_bound!, all eight lanes including duplicates. -/
  | physical (state : State Demand) (owner : RowKey) (lane : Lane) (item : Endpoint)
      (side : Polarity) (selected : insertionLane owner side item = some lane) :
      Write state (appendPhysical state owner lane item)
  /-- relation_with_scoped fresh-key branch; reuse is `reuseRelation`. -/
  | relation (state : State Demand) (record : Relation) :
      Write state { state with relations := state.relations ++ [record] }
  /-- relation_with_scoped fresh nondefault ScopedFlow branch. -/
  | flow (state : State Demand) (record : Flow Demand) :
      Write state { state with flows := state.flows ++ [record] }
  /-- intern_scope fresh nonidentity branch; physical id is old length + 1. -/
  | transformer (state : State Demand) (record : Transformer)
      (nonidentity : record ≠ NativeScopeTransformer.identity) :
      Write state { state with transformers := state.transformers ++ [record] }
  /-- compress_candidate_forests; this is the parent-pointer write footprint. -/
  | compress (state : State Demand) (row root : RowKey) :
      Write state { state with forest := fun key => if key = row then root else state.forest key }
  /-- merge_candidate_rows AFTER copied append/transport children. -/
  | merge (state : State Demand) (copy parent : RowKey) (different : copy ≠ parent) :
      Write state { state with forest := fun key => if key = copy then parent else state.forest key }
  | reuseRelation (state : State Demand) (id : Nat) (record : Relation)
      (found : at state.relations id = some record) : Write state state
  | reuseFlow (state : State Demand) (id : Nat) (record : Flow Demand)
      (found : scopedFlow state id = some record) : Write state state
  | reuseTransformer (state : State Demand) (id : Nat) (record : Transformer)
      (found : rawTransformer state id = some record) : Write state state
  /-- fresh_{value,effect}_at_level append an EMPTY owner. -/
  | freshEmptyRow (state : State Demand) (row : RowKey)
      (empty : ∀ lane, state.physical row lane = []) : Write state state

theorem Write.frame {before after : State Demand} (step : Write before after) :
    Frame before after := by
  cases step <;> constructor <;> intro index value found
  all_goals first
    | exact found
    | exact at_append_of_some _ _ _ _ found
    | exact appendPhysical_old _ _ _ _ _ _ found

inductive Sequence : State Demand → State Demand → Prop
  | refl (state : State Demand) : Sequence state state
  | cons {first middle last : State Demand} :
      Write first middle → Sequence middle last → Sequence first last

theorem Sequence.frame {before after : State Demand} (steps : Sequence before after) :
    Frame before after := by
  induction steps with
  | refl state => exact Frame.refl state
  | cons step rest ih => exact step.frame.trans ih

/-- Frozen identities for ONE invocation; no existential sibling matching. -/
structure ReadbackWitness (Demand : Type) where
  emission : Emission
  admission : Admission
  relationId : Nat
  relation : Relation
  flow : Flow Demand
  transformer : Transformer

structure Readback (state : State Demand) (emissionId : Nat)
    (witness : ReadbackWitness Demand) : Prop where
  emissionFound : at state.emissions emissionId = some witness.emission
  admissionFound : at state.admissions witness.emission.admission = some witness.admission
  admissionBound : witness.admission.bound = witness.emission.bound
  admissionRelation : witness.admission.relation = some witness.relationId
  relationFound : at state.relations witness.relationId = some witness.relation
  flowFound : scopedFlow state witness.relation.scoped = some witness.flow
  transformerFound : rawTransformer state witness.flow.transformer = some witness.transformer
  readbackSlot : witness.emission.readbackSlot = witness.emission.physical
  readbackBound : witness.emission.readbackBound = witness.emission.bound
  physicalFound : physicalKey state witness.emission.physical = some witness.emission.bound

theorem Readback.frame {before after : State Demand} {emissionId : Nat}
    {witness : ReadbackWitness Demand}
    (frame : Frame before after) (record : Readback before emissionId witness) :
    Readback after emissionId witness :=
  { record with
    emissionFound := frame.emissions _ _ record.emissionFound
    admissionFound := frame.admissions _ _ record.admissionFound
    relationFound := frame.relations _ _ record.relationFound
    flowFound := frame.scoped_flow _ _ record.flowFound
    transformerFound := frame.raw_transformer _ _ record.transformerFound
    physicalFound := frame.physical_key _ _ record.physicalFound }

/-- This creates the SAME emission id returned by native `emit`: old length.
It derives lookup at creation; no desired post-state lookup is an argument. -/
def emit (state : State Demand) (record : Emission) : State Demand :=
  { state with emissions := state.emissions ++ [record] }

theorem emit_lookup (state : State Demand) (record : Emission) :
    at (emit state record).emissions state.emissions.length = some record :=
  at_append_end _ _

/-- Creation-side join from the emitter's inputs. No emission-row lookup is
assumed: it is computed from the append. Other lookups here are the actual
local inputs to emit, before any child sequence, not completed-state premises.
-/
theorem emit_readback
    (state : State Demand) (witness : ReadbackWitness Demand)
    (admitted : at state.admissions witness.emission.admission = some witness.admission)
    (sameBound : witness.admission.bound = witness.emission.bound)
    (sameRelation : witness.admission.relation = some witness.relationId)
    (relation : at state.relations witness.relationId = some witness.relation)
    (flow : scopedFlow state witness.relation.scoped = some witness.flow)
    (transformer : rawTransformer state witness.flow.transformer = some witness.transformer)
    (slot : witness.emission.readbackSlot = witness.emission.physical)
    (bound : witness.emission.readbackBound = witness.emission.bound)
    (physical : physicalKey state witness.emission.physical = some witness.emission.bound) :
    Readback (emit state witness.emission) state.emissions.length witness := by
  exact ⟨emit_lookup state witness.emission, admitted, sameBound, sameRelation,
    relation, flow, transformer, slot, bound, physical⟩

def insertionSlot (state : State Demand) (owner : RowKey) (lane : Lane) : Slot :=
  ⟨owner, lane, (state.physical owner lane).length⟩

/-- The admission and physical append computed before EvidenceStore::emit. -/
def bootstrap (state : State Demand) (admission : Admission)
    (owner : RowKey) (lane : Lane) : State Demand :=
  appendPhysical { state with admissions := state.admissions ++ [admission] }
    owner lane admission.bound.item

def insertionEmission (state : State Demand) (admission : Admission)
    (owner : RowKey) (lane : Lane) (previous : Option Nat) : Emission :=
  { admission := state.admissions.length
    bound := admission.bound
    physical := insertionSlot state owner lane
    readbackSlot := insertionSlot state owner lane
    readbackBound := admission.bound
    previousOnGroup := previous }

theorem bootstrap_admission (state : State Demand) (admission : Admission)
    (owner : RowKey) (lane : Lane) :
    at (bootstrap state admission owner lane).admissions state.admissions.length =
      some admission :=
  at_append_end _ _

theorem bootstrap_physical (state : State Demand) (admission : Admission)
    (owner : RowKey) (lane : Lane)
    (fits : laneFits owner lane = true)
    (bound : admission.bound = ⟨rowEndpoint owner, laneSide lane, admission.bound.item⟩) :
    physicalKey (bootstrap state admission owner lane) (insertionSlot state owner lane) =
      some admission.bound := by
  unfold physicalKey
  rw [if_pos fits]
  have appended : physicalAt (bootstrap state admission owner lane)
      (insertionSlot state owner lane) = some admission.bound.item :=
    appendPhysical_new { state with admissions := state.admissions ++ [admission] }
      owner lane admission.bound.item
  rw [appended]
  exact congrArg some bound.symm

def insertionWitness (state : State Demand) (admission : Admission)
    (owner : RowKey) (lane : Lane) (previous : Option Nat)
    (relationId : Nat) (relation : Relation) (flow : Flow Demand)
    (transformer : Transformer) : ReadbackWitness Demand :=
  ⟨insertionEmission state admission owner lane previous,
    admission, relationId, relation, flow, transformer⟩

/-- Both the newly addressed slot and admission lookup are derived here.
The pre-existing relation/flow/raw-transformer chain is a local source input.
Successful native construction of that chain is a separate correspondence
obligation, as are resource checks and finite-word index conversions. -/
theorem bootstrap_emit_readback
    (state : State Demand) (admission : Admission) (owner : RowKey) (lane : Lane)
    (previous : Option Nat) (relationId : Nat) (relation : Relation)
    (flow : Flow Demand) (transformer : Transformer)
    (fits : laneFits owner lane = true)
    (bound : admission.bound = ⟨rowEndpoint owner, laneSide lane, admission.bound.item⟩)
    (sameRelation : admission.relation = some relationId)
    (relationFound : at state.relations relationId = some relation)
    (flowFound : scopedFlow state relation.scoped = some flow)
    (transformerFound : rawTransformer state flow.transformer = some transformer) :
    Readback
      (emit (bootstrap state admission owner lane)
        (insertionEmission state admission owner lane previous))
      state.emissions.length
      (insertionWitness state admission owner lane previous relationId relation flow transformer) := by
  apply emit_readback
  · exact bootstrap_admission state admission owner lane
  · rfl
  · exact sameRelation
  · exact relationFound
  · exact flowFound
  · exact transformerFound
  · rfl
  · rfl
  · exact bootstrap_physical state admission owner lane fits bound

/-- A *model* of the saved-count/live-index successful restoration control.
Each child write must have an explicit `Write` constructor. The saved emission
is immutable and return is allowed exactly at n=count, like the first native
branch in candidate_step_bound_restoration_child. The actual Rust call-to-
sequence theorem is missing; this relation must not be named a native receipt.
The operation id is a shared index throughout, rather than a reselected child.
-/
inductive ModelDriverReturns (operation saved count : Nat) :
    State Demand → Nat → Bool → State Demand → Nat → Prop
  | returned (state : State Demand) (active : Bool) :
      ModelDriverReturns operation saved count state count active state saved
  | write {first middle last : State Demand} {next : Nat} {active : Bool} {out : Nat} :
      Write first middle →
      ModelDriverReturns operation saved count middle next active last out →
      ModelDriverReturns operation saved count first next active last out
  | beginReplay {first last : State Demand} {next out : Nat} (pending : next < count) :
      ModelDriverReturns operation saved count first next true last out →
      ModelDriverReturns operation saved count first next false last out
  | finishReplay {first last : State Demand} {next out : Nat} (pending : next < count) :
      ModelDriverReturns operation saved count first (next + 1) false last out →
      ModelDriverReturns operation saved count first next true last out

theorem ModelDriverReturns.frame_and_return
    {operation saved count next out : Nat} {active : Bool} {before after : State Demand}
    (run : ModelDriverReturns operation saved count before next active after out) :
    Frame before after ∧ out = saved := by
  induction run with
  | returned state active => exact ⟨Frame.refl state, rfl⟩
  | write step rest ih => exact ⟨step.frame.trans ih.1, ih.2⟩
  | beginReplay pending rest ih => exact ih
  | finishReplay pending rest ih => exact ih

theorem model_completed_emission_lookup
    (state : State Demand) (record : Emission) (operation count out : Nat)
    (after : State Demand)
    (run : ModelDriverReturns operation state.emissions.length count
      (emit state record) 0 false after out) :
    out = state.emissions.length ∧ at after.emissions out = some record := by
  obtain ⟨frame, returned⟩ := run.frame_and_return
  refine ⟨returned, ?_⟩
  rw [returned]
  exact frame.emissions _ _ (emit_lookup state record)

theorem model_completed_readback
    (before after : State Demand) (operation saved count next out : Nat) (active : Bool)
    (witness : ReadbackWitness Demand) (created : Readback before saved witness)
    (run : ModelDriverReturns operation saved count before next active after out) :
    out = saved ∧ Readback after out witness := by
  obtain ⟨frame, returned⟩ := run.frame_and_return
  refine ⟨returned, ?_⟩
  rw [returned]
  exact Readback.frame frame created

/-- Computed emitter return followed by explicit modeled successful writes.
This is a conditional local theorem, not the unproved native simulation.
`witness` is unchanged in the conclusion, including every referenced id.
-/
theorem emitted_model_completed_readback
    (state after : State Demand) (witness : ReadbackWitness Demand)
    (operation count out : Nat)
    (admitted : at state.admissions witness.emission.admission = some witness.admission)
    (sameBound : witness.admission.bound = witness.emission.bound)
    (sameRelation : witness.admission.relation = some witness.relationId)
    (relation : at state.relations witness.relationId = some witness.relation)
    (flow : scopedFlow state witness.relation.scoped = some witness.flow)
    (transformer : rawTransformer state witness.flow.transformer = some witness.transformer)
    (slot : witness.emission.readbackSlot = witness.emission.physical)
    (bound : witness.emission.readbackBound = witness.emission.bound)
    (physical : physicalKey state witness.emission.physical = some witness.emission.bound)
    (run : ModelDriverReturns operation state.emissions.length count
      (emit state witness.emission) 0 false after out) :
    out = state.emissions.length ∧ Readback after out witness := by
  exact model_completed_readback (emit state witness.emission) after operation
    state.emissions.length count 0 out false witness
    (emit_readback state witness admitted sameBound sameRelation relation flow
      transformer slot bound physical) run

/-! Transactional failure is a different relation: rollback can remove appended
rows. No frame/lookup theorem for rollback is asserted. Original source roots
are imported solely to identify the parent; there is no new root instance. -/
inductive TransactionFailure (checkpoint : State Demand) : State Demand → State Demand → Prop
  | rollback (failed : State Demand) : TransactionFailure checkpoint failed checkpoint

end YulangClosure.NativeRestorationFrameR4

/-! Audit commands for the primary's post-review single pinned execution.
These commands have not been executed by this leaf. -/
#check @YulangClosure.NativeRestorationFrameR4.at_append_of_some
#print axioms YulangClosure.NativeRestorationFrameR4.at_append_of_some
#check @YulangClosure.NativeRestorationFrameR4.at_append_end
#print axioms YulangClosure.NativeRestorationFrameR4.at_append_end
#check @YulangClosure.NativeRestorationFrameR4.appendPhysical_old
#print axioms YulangClosure.NativeRestorationFrameR4.appendPhysical_old
#check @YulangClosure.NativeRestorationFrameR4.appendPhysical_new
#print axioms YulangClosure.NativeRestorationFrameR4.appendPhysical_new
#check @YulangClosure.NativeRestorationFrameR4.Frame.refl
#print axioms YulangClosure.NativeRestorationFrameR4.Frame.refl
#check @YulangClosure.NativeRestorationFrameR4.Frame.trans
#print axioms YulangClosure.NativeRestorationFrameR4.Frame.trans
#check @YulangClosure.NativeRestorationFrameR4.Frame.physical_key
#print axioms YulangClosure.NativeRestorationFrameR4.Frame.physical_key
#check @YulangClosure.NativeRestorationFrameR4.Frame.raw_transformer
#print axioms YulangClosure.NativeRestorationFrameR4.Frame.raw_transformer
#check @YulangClosure.NativeRestorationFrameR4.Frame.scoped_flow
#print axioms YulangClosure.NativeRestorationFrameR4.Frame.scoped_flow
#check @YulangClosure.NativeRestorationFrameR4.Write.frame
#print axioms YulangClosure.NativeRestorationFrameR4.Write.frame
#check @YulangClosure.NativeRestorationFrameR4.Sequence.frame
#print axioms YulangClosure.NativeRestorationFrameR4.Sequence.frame
#check @YulangClosure.NativeRestorationFrameR4.Readback.frame
#print axioms YulangClosure.NativeRestorationFrameR4.Readback.frame
#check @YulangClosure.NativeRestorationFrameR4.emit_lookup
#print axioms YulangClosure.NativeRestorationFrameR4.emit_lookup
#check @YulangClosure.NativeRestorationFrameR4.emit_readback
#print axioms YulangClosure.NativeRestorationFrameR4.emit_readback
#check @YulangClosure.NativeRestorationFrameR4.bootstrap_admission
#print axioms YulangClosure.NativeRestorationFrameR4.bootstrap_admission
#check @YulangClosure.NativeRestorationFrameR4.bootstrap_physical
#print axioms YulangClosure.NativeRestorationFrameR4.bootstrap_physical
#check @YulangClosure.NativeRestorationFrameR4.bootstrap_emit_readback
#print axioms YulangClosure.NativeRestorationFrameR4.bootstrap_emit_readback
#check @YulangClosure.NativeRestorationFrameR4.ModelDriverReturns.frame_and_return
#print axioms YulangClosure.NativeRestorationFrameR4.ModelDriverReturns.frame_and_return
#check @YulangClosure.NativeRestorationFrameR4.model_completed_emission_lookup
#print axioms YulangClosure.NativeRestorationFrameR4.model_completed_emission_lookup
#check @YulangClosure.NativeRestorationFrameR4.model_completed_readback
#print axioms YulangClosure.NativeRestorationFrameR4.model_completed_readback
#check @YulangClosure.NativeRestorationFrameR4.emitted_model_completed_readback
#print axioms YulangClosure.NativeRestorationFrameR4.emitted_model_completed_readback
