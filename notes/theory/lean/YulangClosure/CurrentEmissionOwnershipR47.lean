import YulangClosure.InternalPermissionIncidenceR45

/-!
R47 conditional current-emission ownership checker. Every edge is checked at
its owning record; current physical storage is reconstructed by raw owner,
lane and index. Bound equality is not used to discover event identity.
Concrete Rust extraction/completeness and same-live-State lifetime equations
remain source obligations. This is not provider arrival, Catch or subtraction.
-/
namespace YulangClosure.CurrentEmissionOwnershipR47

open InternalPermissionIncidenceR45

inductive RowKey (Id : Type) where
  | value (raw : Id) | effect (raw : Id)
  deriving DecidableEq

inductive Endpoint (Id : Type) where
  | valueRow (raw : Id) | effectRow (raw : Id)
  | valueAtom (key : Id) | effectAtom (key : Id)
  deriving DecidableEq

inductive Polarity where
  | positive | negative
  deriving DecidableEq

structure Bound (Id : Type) where
  owner : RowKey Id
  polarity : Polarity
  item : Endpoint Id
  deriving DecidableEq

def rowEndpoint {Id : Type} : RowKey Id → Endpoint Id
  | .value raw => .valueRow raw
  | .effect raw => .effectRow raw

def boundPair {Id : Type} (bound : Bound Id) : Endpoint Id × Endpoint Id :=
  match bound.polarity with
  | .positive => (bound.item, rowEndpoint bound.owner)
  | .negative => (rowEndpoint bound.owner, bound.item)

inductive Lane where
  | valueLowerRow | valueUpperRow | valueLowerAtom | valueUpperAtom
  | effectLowerRow | effectUpperRow | effectLowerAtom | effectUpperAtom
  deriving DecidableEq

structure Slot (Id : Type) where
  owner : RowKey Id
  lane : Lane
  index : Nat
  deriving DecidableEq

structure RowBounds (Id : Type) where
  lowerRows : List Id
  upperRows : List Id
  lowerAtoms : List Id
  upperAtoms : List Id

structure Admission (Id : Type) where
  bound : Bound Id
  relation : Option Nat
  deriving DecidableEq

/-- The only represented phase is the actual constructor-after-append phase;
this historical readback is checked separately from the current row vectors. -/
structure Readback (Id : Type) where
  slot : Slot Id
  bound : Bound Id
  deriving DecidableEq

structure Emission (Id : Type) where
  admission : Nat
  bound : Bound Id
  physical : Slot Id
  readback : Readback Id
  deriving DecidableEq

structure Inputs (Artifact Id Fact : Type) where
  artifact : Artifact
  admissions : List (Admission Id)
  emissions : List (Emission Id)
  valueRows : Id → Option (RowBounds Id)
  effectRows : Id → Option (RowBounds Id)
  liveRelations : List Nat
  dependencies : List (Nat × Nat)
  relationPair : Nat → Option (Endpoint Id × Endpoint Id)
  rootSource : Nat → Option (Id × Nat)
  sourceFact : Id × Nat → Option Fact
  /-- Actual completed Origin/drain candidates matching exact source cause/task. -/
  rootCandidates : UseId Artifact Id → Fact → List Nat
  rootCause : Nat → Option (Id × Nat)
  /-- Actual drain task reconciled with that admitted source FactId's pair. -/
  rootTask : Nat → Option Fact
  rootCompleted : Nat → Bool

structure Query (Artifact Id Fact : Type) where
  use : UseId Artifact Id
  internalFact : Fact
  rawEntry : Id
  rootRelation : Nat
  deriving DecidableEq

structure Probe (Id : Type) where
  admissionIndex : Nat
  emissionIndex : Nat
  admission : Admission Id
  emission : Emission Id
  relation : Nat
  ancestry : List Nat
  deriving DecidableEq

structure Certificate (Artifact Id Fact : Type) where
  query : Query Artifact Id Fact
  evidence : Probe Id
  deriving DecidableEq

variable {Artifact Id Fact : Type} [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]

/-- All eight actual physical lanes. A wrong row-kind/lane pair is unavailable.
Ids in atom vectors preserve their complete typed native endpoint constructor. -/
def currentBound (e : Inputs Artifact Id Fact) (slot : Slot Id) : Option (Bound Id) := do
  match slot.owner, slot.lane with
  | .value row, .valueLowerRow =>
      let bounds ← e.valueRows row
      let item ← bounds.lowerRows[slot.index]?
      some ⟨slot.owner, .positive, .valueRow item⟩
  | .value row, .valueUpperRow =>
      let bounds ← e.valueRows row
      let item ← bounds.upperRows[slot.index]?
      some ⟨slot.owner, .negative, .valueRow item⟩
  | .value row, .valueLowerAtom =>
      let bounds ← e.valueRows row
      let item ← bounds.lowerAtoms[slot.index]?
      some ⟨slot.owner, .positive, .valueAtom item⟩
  | .value row, .valueUpperAtom =>
      let bounds ← e.valueRows row
      let item ← bounds.upperAtoms[slot.index]?
      some ⟨slot.owner, .negative, .valueAtom item⟩
  | .effect row, .effectLowerRow =>
      let bounds ← e.effectRows row
      let item ← bounds.lowerRows[slot.index]?
      some ⟨slot.owner, .positive, .effectRow item⟩
  | .effect row, .effectUpperRow =>
      let bounds ← e.effectRows row
      let item ← bounds.upperRows[slot.index]?
      some ⟨slot.owner, .negative, .effectRow item⟩
  | .effect row, .effectLowerAtom =>
      let bounds ← e.effectRows row
      let item ← bounds.lowerAtoms[slot.index]?
      some ⟨slot.owner, .positive, .effectAtom item⟩
  | .effect row, .effectUpperAtom =>
      let bounds ← e.effectRows row
      let item ← bounds.upperAtoms[slot.index]?
      some ⟨slot.owner, .negative, .effectAtom item⟩
  | _, _ => none

def emissionsForSlot (e : Inputs Artifact Id Fact) (slot : Slot Id) :=
  e.emissions.filter (fun emission => emission.physical == slot)

def ancestryCheck (e : Inputs Artifact Id Fact) : Nat → List Nat → Nat → Bool
  | r, [], target => decide (r = target ∧ r ∈ e.liveRelations)
  | r, child :: rest, target => decide (r ∈ e.liveRelations ∧ (r, child) ∈ e.dependencies) &&
      ancestryCheck e child rest target

inductive RelationPath (e : Inputs Artifact Id Fact) : Nat → Nat → Prop where
  | refl {r} : r ∈ e.liveRelations → RelationPath e r r
  | step {r child target} : r ∈ e.liveRelations → (r, child) ∈ e.dependencies →
      RelationPath e child target → RelationPath e r target

omit [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact] in
theorem ancestry_sound (e : Inputs Artifact Id Fact) (root target : Nat) (path : List Nat)
    (checked : ancestryCheck e root path target = true) : RelationPath e root target := by
  induction path generalizing root with
  | nil =>
    have h : root = target ∧ root ∈ e.liveRelations := by simpa [ancestryCheck] using checked
    cases h.1
    exact .refl h.2
  | cons child rest ih =>
    have h : (root ∈ e.liveRelations ∧ (root, child) ∈ e.dependencies) ∧
        ancestryCheck e child rest target = true := by simpa [ancestryCheck] using checked
    exact .step h.1.1 h.1.2 (ih child h.2)

/-- Source root selection checks the completed Origin/drain occurrence, cause
and task against the same admitted Internal source fact; no endpoint-only root. -/
def RootMatches (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) : Prop :=
  q.use.artifact = e.artifact ∧ e.rootCandidates q.use q.internalFact = [q.rootRelation] ∧
  e.rootSource q.rootRelation = some (q.use.occurrence, 0) ∧
  e.rootCause q.rootRelation = some (q.use.occurrence, 0) ∧
  e.rootTask q.rootRelation = some q.internalFact ∧ e.rootCompleted q.rootRelation = true ∧
  e.sourceFact (q.use.occurrence, 0) = some q.internalFact

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) :
    Decidable (RootMatches e q) := by unfold RootMatches; infer_instance

/-- Local checked joins, not an assumed aggregate ownership/arrival predicate.
The admission is selected by its exact index; physical-slot ambiguity rejects. -/
def Matches (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) : Prop :=
  e.admissions[p.admissionIndex]? = some p.admission ∧
  e.emissions[p.emissionIndex]? = some p.emission ∧
  p.emission.admission = p.admissionIndex ∧
  emissionsForSlot e p.emission.physical = [p.emission] ∧
  p.emission.bound = p.admission.bound ∧ p.emission.readback.slot = p.emission.physical ∧
  p.emission.readback.bound = p.admission.bound ∧
  currentBound e p.emission.physical = some p.admission.bound ∧
  p.admission.relation = some p.relation ∧
  e.relationPair p.relation = some (boundPair p.admission.bound) ∧
  ancestryCheck e q.rootRelation p.ancestry p.relation = true ∧
  RootMatches e q ∧
  p.emission.physical.owner = .effect q.rawEntry ∧
  p.admission.bound.owner = .effect q.rawEntry ∧ p.admission.bound.polarity = .positive

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) :
    Decidable (Matches e q p) := by unfold Matches; infer_instance

def extract (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id) :
    Option (Certificate Artifact Id Fact) :=
  if Matches e q p then some ⟨q, p⟩ else none

theorem accepted_iff (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id)
    (out : Certificate Artifact Id Fact) : extract e q p = some out ↔
      Matches e q p ∧ out = ⟨q, p⟩ := by
  by_cases valid : Matches e q p
  · rw [extract, ite_eq_left valid]
    constructor
    · intro equal; exact ⟨valid, (Option.some.inj equal).symm⟩
    · rintro ⟨_, rfl⟩; rfl
  · rw [extract, ite_eq_right valid]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨matched, _⟩; exact False.elim (valid matched)

theorem accepted_current_slot (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (out : Certificate Artifact Id Fact) (accepted : extract e q p = some out) :
    e.emissions[out.evidence.emissionIndex]? = some out.evidence.emission ∧
    e.admissions[out.evidence.emission.admission]? = some out.evidence.admission ∧
    currentBound e out.evidence.emission.physical = some out.evidence.admission.bound ∧
    out.evidence.emission.bound = out.evidence.admission.bound ∧
    out.evidence.emission.readback.slot = out.evidence.emission.physical ∧
    out.evidence.emission.readback.bound = out.evidence.admission.bound := by
  obtain ⟨matched, rfl⟩ := (accepted_iff e q p out).mp accepted
  rcases matched with ⟨admission, emission, id, _, bound, slot, historical, current, _⟩
  exact ⟨emission, id ▸ admission, current, bound, slot, historical⟩

theorem accepted_unique_event (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (out : Certificate Artifact Id Fact) (accepted : extract e q p = some out) :
    e.admissions[out.evidence.emission.admission]? = some out.evidence.admission ∧
      emissionsForSlot e out.evidence.emission.physical = [out.evidence.emission] := by
  obtain ⟨matched, rfl⟩ := (accepted_iff e q p out).mp accepted
  rcases matched with ⟨admission, _, id, unique, _⟩
  exact ⟨id ▸ admission, unique⟩

theorem accepted_same_use_entry (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (out : Certificate Artifact Id Fact) (accepted : extract e q p = some out) :
    out.query = q ∧ RootMatches e out.query ∧
      out.evidence.admission.relation = some out.evidence.relation ∧
      e.relationPair out.evidence.relation = some (boundPair out.evidence.admission.bound) ∧
      RelationPath e out.query.rootRelation out.evidence.relation ∧
      out.evidence.emission.physical.owner = .effect out.query.rawEntry ∧
      out.evidence.admission.bound.owner = .effect out.query.rawEntry ∧
      out.evidence.admission.bound.polarity = .positive := by
  obtain ⟨matched, rfl⟩ := (accepted_iff e q p out).mp accepted
  rcases matched with ⟨_, _, _, _, _, _, _, _, relation, pair, ancestry, root, slot, bound, polarity⟩
  exact ⟨rfl, root, relation, pair, ancestry_sound e q.rootRelation p.relation p.ancestry ancestry,
    slot, bound, polarity⟩

theorem accepted_root_fields (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (out : Certificate Artifact Id Fact) (accepted : extract e q p = some out) :
    out.query.use.artifact = e.artifact ∧
      e.rootCandidates out.query.use out.query.internalFact = [out.query.rootRelation] ∧
      e.rootSource out.query.rootRelation = some (out.query.use.occurrence, 0) ∧
      e.rootCause out.query.rootRelation = some (out.query.use.occurrence, 0) ∧
      e.rootTask out.query.rootRelation = some out.query.internalFact ∧
      e.rootCompleted out.query.rootRelation = true ∧
      e.sourceFact (out.query.use.occurrence, 0) = some out.query.internalFact := by
  exact (accepted_same_use_entry e q p out accepted).2.1

theorem mismatch_rejected (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (mismatch : ¬ Matches e q p) : extract e q p = none := by
  simp [extract, mismatch]

theorem swapped_or_stale_rejected (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id)
    (bad : e.admissions[p.admissionIndex]? ≠ some p.admission ∨
      e.emissions[p.emissionIndex]? ≠ some p.emission ∨
      p.emission.admission ≠ p.admissionIndex ∨
      emissionsForSlot e p.emission.physical ≠ [p.emission] ∨
      p.emission.bound ≠ p.admission.bound ∨ p.emission.readback.slot ≠ p.emission.physical ∨
      p.emission.readback.bound ≠ p.admission.bound ∨
      currentBound e p.emission.physical ≠ some p.admission.bound) : extract e q p = none := by
  apply mismatch_rejected
  rintro ⟨ha, he, hi, hs, hb, hr, hh, hc, _⟩
  rcases bad with h | h | h | h | h | h | h | h <;> contradiction

theorem foreign_use_or_entry_rejected (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id)
    (foreign : p.admission.relation ≠ some p.relation ∨
      e.relationPair p.relation ≠ some (boundPair p.admission.bound) ∨
      ancestryCheck e q.rootRelation p.ancestry p.relation ≠ true ∨ ¬ RootMatches e q ∨
      p.emission.physical.owner ≠ .effect q.rawEntry ∨
      p.admission.bound.owner ≠ .effect q.rawEntry ∨ p.admission.bound.polarity ≠ .positive) :
    extract e q p = none := by
  apply mismatch_rejected
  rintro ⟨_, _, _, _, _, _, _, _, hr, pair, ha, root, hp, hb, hv⟩
  rcases foreign with h | h | h | h | h | h | h <;> contradiction

/-- SAME permission witness, without assuming current ownership or arrival as
an aggregate premise: each is reconstructed by the preceding partial checker.
The source still owns the three cross-model extraction equations. -/
theorem apply_to_internal {Term : Type} [DecidableEq Term]
    (internalInputs : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
    (internalQuery : InternalPermissionIncidenceR45.Query Artifact Id)
    (internalProbe : InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
    (internal : InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
    (internalAccepted : InternalPermissionIncidenceR45.extract internalInputs internalQuery internalProbe = some internal)
    (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) (p : Probe Id)
    (out : Certificate Artifact Id Fact) (accepted : extract e q p = some out)
    (sameUse : q.use = internal.use) (sameFact : q.internalFact = internal.fact)
    (sameRawEntry : q.rawEntry = internal.permission.entry) :
    out.query.use = internal.use ∧ out.query.internalFact = internal.fact ∧
      internal.permission = internalProbe.permission ∧
      internal.permission.concrete = internalProbe.permission.concrete ∧
      currentBound e out.evidence.emission.physical = some out.evidence.admission.bound ∧
      out.evidence.emission.physical.owner = .effect internal.permission.entry ∧
      RelationPath e out.query.rootRelation out.evidence.relation := by
  have current := accepted_current_slot e q p out accepted
  have ownership := accepted_same_use_entry e q p out accepted
  have payload := InternalPermissionIncidenceR45.accepted_payload internalInputs internalQuery internalProbe internal internalAccepted
  obtain ⟨_, rfl⟩ := (accepted_iff e q p out).mp accepted
  exact ⟨sameUse, sameFact, payload.1, payload.2.2.1, current.2.2.1,
    sameRawEntry ▸ ownership.2.2.2.2.2.1, ownership.2.2.2.2.1⟩

/-- Finite checked records, not Rust construction or execution receipts. -/
def witnessBound : Bound Nat := ⟨.effect 4, .positive, .effectAtom 7⟩
def witnessSlot : Slot Nat := ⟨.effect 4, .effectLowerAtom, 0⟩
def witnessAdmission : Admission Nat := ⟨witnessBound, some 1⟩
def witnessEmission : Emission Nat := ⟨0, witnessBound, witnessSlot, ⟨witnessSlot, witnessBound⟩⟩
def witnessQuery : Query Nat Nat Nat := ⟨⟨99, 100⟩, 88, 4, 0⟩
def witnessProbe : Probe Nat := ⟨0, 0, witnessAdmission, witnessEmission, 1, [1]⟩
def witnessInputs : Inputs Nat Nat Nat :=
  ⟨99, [witnessAdmission], [witnessEmission], (fun _ => none),
    (fun row => if row = 4 then some ⟨[], [], [7], []⟩ else none),
    [0, 1], [(0, 1)],
    (fun r => if r = 1 then some (boundPair witnessBound) else none),
    (fun r => if r = 0 then some (100, 0) else none),
    (fun key => if key = (100, 0) then some 88 else none),
    (fun use fact => if use = witnessQuery.use ∧ fact = 88 then [0] else []),
    (fun r => if r = 0 then some (100, 0) else none),
    (fun r => if r = 0 then some 88 else none), (fun r => r == 0)⟩

theorem concrete_current_event_witness :
    extract witnessInputs witnessQuery witnessProbe = some ⟨witnessQuery, witnessProbe⟩ ∧
      currentBound witnessInputs witnessSlot = some witnessBound := by decide

theorem concrete_swapped_stale_foreign_rejected :
    extract witnessInputs witnessQuery { witnessProbe with emissionIndex := 1 } = none ∧
    extract witnessInputs witnessQuery
      { witnessProbe with emission := { witnessEmission with physical := ⟨.effect 4, .effectLowerAtom, 1⟩ } } = none ∧
    extract { witnessInputs with effectRows := fun _ => none } witnessQuery witnessProbe = none ∧
    extract { witnessInputs with emissions := [witnessEmission, witnessEmission] } witnessQuery witnessProbe = none ∧
    extract witnessInputs { witnessQuery with use := ⟨98, 100⟩ } witnessProbe = none ∧
    extract witnessInputs { witnessQuery with rawEntry := 5 } witnessProbe = none := by decide

end YulangClosure.CurrentEmissionOwnershipR47
