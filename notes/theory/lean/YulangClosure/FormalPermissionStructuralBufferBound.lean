import YulangClosure.FormalPermissionEventBuffer

/-! R18: conditional positive-tuple trace, term.rs:1272–1303, 1352–1385,
1083–1201; candidate_effect.rs:1617–1659; lib.rs:10594–10622.
Primitive records are supplied observations, never authenticated Rust receipts.
No existence of a native state satisfying Conditions is asserted. -/
namespace YulangClosure.FormalPermissionStructuralBufferBound
open FormalPermissionArenaEvents FormalPermissionEventBuffer
open FormalPermissionTermCallControl FormalPermissionHelperFrames
noncomputable section

/-- Success and capacity change are distinct observations of the SAME call. -/
structure ReserveReceipt where
  beforeCapacity : Nat
  afterCapacity : Nat
  result : Except Nat Unit
  snapshot : EventOutcome

def ReserveReceipt.grewSuccessfully (r : ReserveReceipt) : Prop :=
  r.result = .ok () ∧ r.beforeCapacity ≠ r.afterCapacity

def ReserveReceipt.outcome (r : ReserveReceipt) : ReserveOutcome :=
  ⟨decide (r.beforeCapacity ≠ r.afterCapacity), (match r.result with | .ok _ => true | .error _ => false), r.snapshot⟩

structure TupleInput where
  children : List Nat
  lookup : Nat → Option Nat
  positiveValueEndpoint : Nat → Bool
  tupleCopyReserve : Except Nat Unit
  arcBacking : Option Nat
  backingIdentity : Nat
  payloadBytes : Except Nat Nat
  structuralReserve : Except Nat Unit
  cacheLookup : Option Nat
  journalPresent : Bool
  pageNeeded : Bool
  interner : ReserveReceipt
  internedJournal : ReserveReceipt
  pageDescriptors : ReserveReceipt
  pagePositions : ReserveReceipt
  claimedPagesJournal : ReserveReceipt
  pageAllocation : Except Nat Nat
  pageClaim : Except Nat Nat
  internResult : Except Nat Nat
  pageSnapshot : EventOutcome
  structuralSnapshot : EventOutcome

/-- Local premises for the successful intern branch. The shared cache observation
belongs to intern_structure and intern: structural reserve does not mutate
positions. Children retain identity. Arc construction, payload arithmetic,
allocation, claim and intern success remain separate explicit premises. -/
structure Conditions (i : TupleInput) : Prop where
  nonempty : i.children ≠ []
  childrenValid : ∀ child ∈ i.children, ∃ node,
    i.lookup child = some node ∧ i.positiveValueEndpoint node = true
  copyReserved : i.tupleCopyReserve = .ok ()
  arcMaterialized : i.arcBacking = some i.backingIdentity
  payloadChecked : ∃ bytes, i.payloadBytes = .ok bytes
  structuralReserved : i.structuralReserve = .ok ()
  cacheMiss : i.cacheLookup = none
  activeJournal : i.journalPresent = true
  needsPage : i.pageNeeded = true
  internerGrowth : i.interner.grewSuccessfully
  internedGrowth : i.internedJournal.grewSuccessfully
  descriptorsGrowth : i.pageDescriptors.grewSuccessfully
  positionsGrowth : i.pagePositions.grewSuccessfully
  claimedGrowth : i.claimedPagesJournal.grewSuccessfully
  allocated : ∃ address, i.pageAllocation = .ok address
  claimed : ∃ base, i.pageClaim = .ok base
  interned : ∃ term, i.internResult = .ok term

/-- Reuse only R16's mode-independent intern protocol. The administrative mode
field is ignored by protocol; starts/valid/appended are NOT used to classify a
tuple as a live variable or function. Tuple guards are Conditions. -/
def internInput (i : TupleInput) : Input where
  mode := .liveVariable
  childrenValid := true
  cacheHit := false
  journalPresent := i.journalPresent
  pageNeeded := i.pageNeeded
  interner := i.interner.outcome
  internedJournal := i.internedJournal.outcome
  pageDescriptors := i.pageDescriptors.outcome
  pagePositions := i.pagePositions.outcome
  claimedPagesJournal := i.claimedPagesJournal.outcome
  publication := match i.pageAllocation, i.pageClaim with
    | .ok _, .ok _ => .published
    | _, _ => .allocationFailed
  backingObservation := i.pageSnapshot

/-- Computed from the ordered source reserve/publication protocol. -/
def internEvents (i : TupleInput) : List Event := run (protocol (internInput i))

def internSnapshots (i : TupleInput) : List EventOutcome :=
  (internEvents i).map Event.observation

/-- Reached only under Conditions, after intern returns Ok; structural snapshot
is unconditional even if structural_backings capacity did not change. -/
def attemptedSnapshots (i : TupleInput) : List EventOutcome :=
  internSnapshots i ++ [i.structuralSnapshot]

private theorem reserve_success (r : ReserveReceipt) (h : r.grewSuccessfully) :
    r.outcome.changed = true ∧ r.outcome.succeeded = true := by
  simp [ReserveReceipt.outcome, h.1, h.2]

theorem intern_events_exact (i : TupleInput) (h : Conditions i) :
    internEvents i =
      [⟨.interner, i.interner.snapshot⟩,
       ⟨.internedJournal, i.internedJournal.snapshot⟩,
       ⟨.pageDescriptors, i.pageDescriptors.snapshot⟩,
       ⟨.pagePositions, i.pagePositions.snapshot⟩,
       ⟨.claimedPagesJournal, i.claimedPagesJournal.snapshot⟩,
       ⟨.pageBacking, i.pageSnapshot⟩] := by
  have a := reserve_success i.interner h.internerGrowth
  have b := reserve_success i.internedJournal h.internedGrowth
  have c := reserve_success i.pageDescriptors h.descriptorsGrowth
  have d := reserve_success i.pagePositions h.positionsGrowth
  have e := reserve_success i.claimedPagesJournal h.claimedGrowth
  obtain ⟨address, allocated⟩ := h.allocated
  obtain ⟨base, claimed⟩ := h.claimed
  simp [internEvents, protocol, internInput, reserve, publicationAttempt,
    published, run, emitted, h.activeJournal, h.needsPage, allocated, claimed,
    a.1, a.2, b.1, b.2, c.1, c.2, d.1, d.2, e.1, e.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem intern_length (i : TupleInput) (h : Conditions i) :
    (internSnapshots i).length = 6 := by
  simp [internSnapshots, intern_events_exact i h]

/-- Assertion precedes any array write/increment. Failure records the attempted
zero-based index and physical size; it is not a recoverable Except.Err. -/
inductive PushResult where
  | stored : Buffer EventOutcome → PushResult
  | assertionFailure : Nat → Nat → PushResult

def attemptPush (b : Buffer EventOutcome) (x : EventOutcome) : PushResult :=
  if free : b.len < 6 then .stored (push b x free)
  else .assertionFailure b.len b.snapshots.size

/-- Six successful pushes fill R17's physical Option slots. The structural push
attempts index six and fails the bound assertion. No takeEvents/finish occurs
between these source-ordered operations in this selected local trace. -/
theorem conditional_seventh_assertion (i : TupleInput) (h : Conditions i)
    (entry : Buffer EventOutcome) (emptyEntry : Layout entry []) :
    ∃ full : Buffer EventOutcome,
      Appends entry (internSnapshots i) full ∧
      Layout full (internSnapshots i) ∧
      full.len = 6 ∧
      full.snapshots.toList = (internSnapshots i).map some ∧
      attemptPush full i.structuralSnapshot = .assertionFailure 6 6 := by
  have six := intern_length i h
  obtain ⟨full, execution⟩ := appends_exists entry [] (internSnapshots i)
    emptyEntry (by simpa using Nat.le_of_eq six)
  have layout : Layout full (internSnapshots i) := by
    simpa using appends_layout entry full _ execution [] emptyEntry
  have len : full.len = 6 := layout.len_eq.trans six
  have slots : full.snapshots.toList = (internSnapshots i).map some := by
    simpa [six] using layout.slots_eq
  exact ⟨full, execution, layout, len, slots, by simp [attemptPush, len, full.fixedSize]⟩

/-- The computed attempted suffix admits no normal bounded Appends execution.
A conditional local obstruction; no native state or candidate call is supplied. -/
theorem no_normal_seven_pushes (i : TupleInput) (h : Conditions i)
    (entry : Buffer EventOutcome) (emptyEntry : Layout entry []) :
    ¬ ∃ last, Appends entry (attemptedSnapshots i) last := by
  rintro ⟨last, execution⟩
  have layout := appends_layout entry last _ execution [] emptyEntry
  have bound := layout.bounded
  have six := intern_length i h
  simp [attemptedSnapshots, six] at bound

end
end YulangClosure.FormalPermissionStructuralBufferBound
