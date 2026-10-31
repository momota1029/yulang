import YulangClosure.AuthenticatedResidualConsumerR49

/-!
R51 finite partial native publication observation. Inputs are retained native
owner reads, not execution axioms. Missing passive completion evidence may
coexist with successful ordinary inference. No source/native completeness,
Catch execution, whole solver soundness or production authority is established.
-/
namespace YulangClosure.NativeResidualPublicationR51

open CurrentEmissionOwnershipR47

deriving instance DecidableEq for CurrentEmissionOwnershipR47.RowBounds

structure ReplayAck where
  operation : Nat
  index : Nat
  deriving DecidableEq

structure Drain (Id : Type) where
  drainIndex : Nat
  incomingRelation : Option Nat
  replayAck : Option ReplayAck
  createdSeed : Nat
  selectedRelation : Nat
  originIndex : Nat
  task : Endpoint Id × Endpoint Id
  cause : Id
  completed : Bool
  deriving DecidableEq

structure OriginalFact (Id Fact : Type) where
  fact : Fact
  occurrence : Id
  slot : Nat
  cause : Id
  lower : Endpoint Id
  upper : Endpoint Id
  deriving DecidableEq

/-- Retained at the actual consumer call, selected by publication/index before
endpoint comparison. Cuts delimit this call's new origins/emissions. -/
structure Call (Id Fact : Type) where
  identity : Nat
  publication : Nat
  planIndex : Nat
  endpoint : Endpoint Id
  upper : Endpoint Id
  fact : Fact
  occurrence : Id
  slot : Nat
  cause : Id
  originCut : Nat
  emissionCut : Nat
  returned : Bool
  deriving DecidableEq

structure Origin (Id : Type) where
  relation : Nat
  occurrence : Id
  slot : Nat
  receipt : Drain Id
  deriving DecidableEq

inductive Mode where
  | newlyEmitted | alreadyPresent
  deriving DecidableEq

structure ForwardProbe (Id Fact : Type) where
  call : Call Id Fact
  receipt : Drain Id
  slot : Slot Id
  bound : Bound Id
  physical : Option (CurrentEmissionOwnershipR47.Probe Id)
  mode : Mode

inductive Probe (Id Fact : Type) where
  | suppressed
  | forwarded (evidence : ForwardProbe Id Fact)

structure Item (Id Fact : Type) where
  index : Nat
  endpoint : Endpoint Id
  decision : AuthenticatedResidualConsumerR49.Decision
  probe : Probe Id Fact

/-- Exact current native reads; their extraction and same-State lifetimes are
explicit source obligations. This is not a second propagation algorithm. -/
structure Inputs (Artifact Id Fact : Type) where
  after : ProviderEntryArrivalR48.Inputs Artifact Id Fact
  facts : Fact → Option (OriginalFact Id Fact)
  callCandidates : Nat → Nat → List (Call Id Fact)
  calls : Nat → Option (Call Id Fact)
  receiptCandidates : Nat → List (Drain Id)
  completionCandidates : Nat → List (Drain Id)
  origins : List (Origin Id)
  /-- Raw upper operand resolves at the actual native result-owner read. -/
  resultOwner : Endpoint Id → Option Id
  /-- Snapshot taken before this exact call, not a post-hoc endpoint search. -/
  beforeBound : Nat → Slot Id → Option (Bound Id)
  newEmissions : Nat → Slot Id → List Nat
  priorEmissionCount : Nat → Slot Id → Nat
  boundCandidates : Id → Endpoint Id → List (Slot Id)
  initialRows : Id → Option (RowBounds Id)

structure Frame (Id : Type) where
  row : Id
  before : RowBounds Id
  after : RowBounds Id
  rowsSuffix : List Id
  atomsSuffix : List Id

structure Query (Artifact Id Term Fact : Type) where
  context : AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact
  publication : Nat
  original : List (Endpoint Id)
  originalFact : OriginalFact Id Fact
  frame : Frame Id
  items : List (Item Id Fact)

variable {Artifact Id Term Fact : Type}
  [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]

/-- Only newly emitted Forward decisions contribute planned append slots.
AlreadyPresent and Suppress contribute no new native lower operand. -/
def plannedRows {Id Fact : Type} (items : List (Item Id Fact)) : List Id :=
  items.filterMap fun item => match item.decision, item.probe with
    | .forward, .forwarded p => match p.mode, p.bound.item with
      | .newlyEmitted, .effectRow raw => some raw
      | _, _ => none
    | _, _ => none

def plannedAtoms {Id Fact : Type} (items : List (Item Id Fact)) : List Id :=
  items.filterMap fun item => match item.decision, item.probe with
    | .forward, .forwarded p => match p.mode, p.bound.item with
      | .newlyEmitted, .effectAtom raw => some raw
      | _, _ => none
    | _, _ => none

def FactReads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Prop :=
  e.facts q.originalFact.fact = some q.originalFact ∧
  q.originalFact.fact = q.context.query.catchFact ∧
  q.originalFact.occurrence = q.context.query.catchOccurrence ∧ q.originalFact.slot = 51 ∧
  q.originalFact.lower = q.context.query.catchInput ∧ q.originalFact.upper = q.context.query.catchOutput

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Decidable (FactReads e q) := by
  unfold FactReads; infer_instance

/-- Checks the current native result vectors against the retained prepublication
vectors. Suffixes are observed finite data, not assumed source frame laws. -/
def FrameReads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Prop :=
  e.resultOwner q.originalFact.upper = some q.frame.row ∧
  e.initialRows q.frame.row = some q.frame.before ∧
  e.after.current.effectRows q.frame.row = some q.frame.after ∧
  q.frame.after.lowerRows = q.frame.before.lowerRows ++ q.frame.rowsSuffix ∧
  q.frame.after.lowerAtoms = q.frame.before.lowerAtoms ++ q.frame.atomsSuffix ∧
  q.frame.rowsSuffix = plannedRows q.items ∧ q.frame.atomsSuffix = plannedAtoms q.items

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Decidable (FrameReads e q) := by
  unfold FrameReads; infer_instance

def CallReads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact) : Prop :=
  e.callCandidates q.publication index = [p.call] ∧ e.calls p.call.identity = some p.call ∧
  p.call.publication = q.publication ∧ p.call.planIndex = index ∧
  p.call.endpoint = endpoint ∧ p.call.upper = q.originalFact.upper ∧
  p.call.fact = q.originalFact.fact ∧ p.call.occurrence = q.originalFact.occurrence ∧
  p.call.slot = q.originalFact.slot ∧ p.call.cause = q.originalFact.cause ∧ p.call.returned = true

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact) :
    Decidable (CallReads e q index endpoint p) := by unfold CallReads; infer_instance

/-- Source-drain attribution uses the complete retained receipt, exact origin
and completion copy. Equal endpoints alone do not select a source drain. -/
def DrainReads (e : Inputs Artifact Id Fact) (p : ForwardProbe Id Fact) : Prop :=
  e.receiptCandidates p.call.identity = [p.receipt] ∧
  e.completionCandidates p.call.identity = [{ p.receipt with completed := true }] ∧
  p.receipt.completed = false ∧ p.call.originCut ≤ p.receipt.originIndex ∧
  e.origins[p.receipt.originIndex]? = some ⟨p.receipt.createdSeed, p.call.occurrence, p.call.slot, p.receipt⟩ ∧
  p.receipt.task = (p.call.endpoint, p.call.upper) ∧ p.receipt.cause = p.call.cause ∧
  p.receipt.selectedRelation = p.receipt.incomingRelation.getD p.receipt.createdSeed ∧
  p.receipt.createdSeed ∈ e.after.current.liveRelations ∧
  p.receipt.selectedRelation ∈ e.after.current.liveRelations ∧
  e.after.current.relationPair p.receipt.selectedRelation = some p.receipt.task

instance (e : Inputs Artifact Id Fact) (p : ForwardProbe Id Fact) : Decidable (DrainReads e p) := by
  unfold DrainReads; infer_instance

/-- AlreadyPresent needs no old emission record. It verifies the native
pre-call bound and unchanged exact-slot count, permitting ZERO prior emissions.
Only NewlyEmitted demands a new owned emission and current-call ancestry. -/
def ModeReads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) (p : ForwardProbe Id Fact) : Prop :=
  match p.mode with
  | .newlyEmitted =>
      ∃ physical ∈ p.physical.toList,
        physical.emission.physical = p.slot ∧ physical.admission.bound = p.bound ∧
        ProviderEntryArrivalR48.EdgeReads e.after (.effectRow q.frame.row) physical ∧
        e.beforeBound p.call.identity p.slot = none ∧
        e.newEmissions p.call.identity p.slot = [physical.emissionIndex] ∧
        e.priorEmissionCount p.call.identity p.slot = 0 ∧
        p.call.emissionCut ≤ physical.emissionIndex ∧
        ancestryCheck e.after.current p.receipt.selectedRelation physical.ancestry physical.relation = true
  | .alreadyPresent =>
      p.physical = none ∧ e.beforeBound p.call.identity p.slot = some p.bound ∧
      e.newEmissions p.call.identity p.slot = [] ∧
      (emissionsForSlot e.after.current p.slot).length = e.priorEmissionCount p.call.identity p.slot

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) (p : ForwardProbe Id Fact) :
    Decidable (ModeReads e q p) := by
  cases hm : p.mode <;> simp only [ModeReads, hm] <;> infer_instance

def ForwardReads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact) : Prop :=
  CallReads e q index endpoint p ∧ DrainReads e p ∧
  e.boundCandidates q.frame.row endpoint = [p.slot] ∧
  currentBound e.after.current p.slot = some p.bound ∧
  p.bound.owner = .effect q.frame.row ∧ p.slot.owner = .effect q.frame.row ∧
  p.bound.item = endpoint ∧ p.bound.polarity = .positive ∧
  (p.slot.lane = .effectLowerRow ∨ p.slot.lane = .effectLowerAtom) ∧ ModeReads e q p

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact) :
    Decidable (ForwardReads e q index endpoint p) := by unfold ForwardReads; infer_instance

def ItemReads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) (item : Item Id Fact) : Prop :=
  match item.decision, item.probe with
  | .suppress, .suppressed => e.callCandidates q.publication item.index = []
  | .forward, .forwarded p => ForwardReads e q item.index item.endpoint p
  | _, _ => False

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) (item : Item Id Fact) :
    Decidable (ItemReads e q item) := by
  cases hd : item.decision <;> cases hp : item.probe <;> simp only [ItemReads, hd, hp] <;> infer_instance

def itemPlan {Id Fact : Type} (items : List (Item Id Fact)) := items.map (fun item => (item.endpoint, item.decision))

def Reads (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Prop :=
  AuthenticatedResidualConsumerR49.plan q.context q.original = some (itemPlan q.items) ∧
  q.items.map Item.index = List.range q.items.length ∧
  e.after.current.artifact = q.context.inputs.arrival.current.artifact ∧
  FactReads e q ∧ FrameReads e q ∧ q.items.all (fun item => decide (ItemReads e q item)) = true

instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Decidable (Reads e q) := by
  unfold Reads; infer_instance

def observe (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) : Bool := decide (Reads e q)

theorem accepted_plan (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) :
    AuthenticatedResidualConsumerR49.plan q.context q.original = some (itemPlan q.items) ∧
    (itemPlan q.items).map Prod.fst = q.original := by
  have h : Reads e q := of_decide_eq_true accepted
  exact ⟨h.1, (AuthenticatedResidualConsumerR49.plan_correspondence _ _ _ h.1).1⟩

theorem accepted_item (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (item : Item Id Fact) (member : item ∈ q.items) : ItemReads e q item := by
  have h : Reads e q := of_decide_eq_true accepted
  have all := (List.all_eq_true.mp h.2.2.2.2.2) item member
  exact of_decide_eq_true all

omit [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact] in
/-- Exact arguments/cause come from the retained consumer call, not a matching
current bound found after the call. -/
theorem forward_exact_arguments (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact)
    (checked : ForwardReads e q index endpoint p) :
    p.call.endpoint = endpoint ∧ p.call.upper = q.originalFact.upper ∧
    p.call.fact = q.originalFact.fact ∧ p.call.occurrence = q.originalFact.occurrence ∧
    p.call.slot = q.originalFact.slot ∧ p.call.cause = q.originalFact.cause ∧
    p.receipt.task = (endpoint, q.originalFact.upper) ∧ p.receipt.cause = q.originalFact.cause := by
  rcases checked with ⟨call, drain, _⟩
  rcases call with ⟨_, _, _, _, endpoint, upper, fact, occurrence, slot, cause, _⟩
  rcases drain with ⟨_, _, _, _, _, task, drainCause, _⟩
  exact ⟨endpoint, upper, fact, occurrence, slot, cause,
    by simpa only [endpoint, upper] using task, drainCause.trans cause⟩

omit [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact] in
theorem forward_current_native (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact)
    (checked : ForwardReads e q index endpoint p) :
    currentBound e.after.current p.slot = some p.bound ∧ p.bound.item = endpoint ∧
    p.bound.owner = .effect q.frame.row ∧ p.slot.owner = .effect q.frame.row ∧
    p.bound.polarity = .positive ∧ (p.slot.lane = .effectLowerRow ∨ p.slot.lane = .effectLowerAtom) ∧
    e.boundCandidates q.frame.row endpoint = [p.slot] := by
  rcases checked with ⟨_, _, unique, current, owner, slot, item, polarity, lane, _⟩
  exact ⟨current, item, owner, slot, polarity, lane, unique⟩

omit [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact] in
theorem new_emission_attributed (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact)
    (checked : ForwardReads e q index endpoint p) (mode : p.mode = .newlyEmitted) :
    ∃ physical, p.physical = some physical ∧
      physical.emission.physical = p.slot ∧ physical.admission.bound = p.bound ∧
      ProviderEntryArrivalR48.EdgeReads e.after (.effectRow q.frame.row) physical ∧
      e.beforeBound p.call.identity p.slot = none ∧
      e.newEmissions p.call.identity p.slot = [physical.emissionIndex] ∧
      e.priorEmissionCount p.call.identity p.slot = 0 ∧
      p.call.emissionCut ≤ physical.emissionIndex ∧
      RelationPath e.after.current p.receipt.selectedRelation physical.relation := by
  have reads := checked.2.2.2.2.2.2.2.2.2
  simp only [ModeReads, mode] at reads
  obtain ⟨physical, member, slot, bound, edge, before, new, prior, cut, path⟩ := reads
  have exactProbe : p.physical = some physical := by simpa using member
  exact ⟨physical, exactProbe, slot, bound, edge, before, new, prior, cut, ancestry_sound _ _ _ _ path⟩

omit [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact] in
theorem already_present_no_new_emission (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact)
    (checked : ForwardReads e q index endpoint p) (mode : p.mode = .alreadyPresent) :
    p.physical = none ∧ e.beforeBound p.call.identity p.slot = some p.bound ∧
      e.newEmissions p.call.identity p.slot = [] ∧
      (emissionsForSlot e.after.current p.slot).length = e.priorEmissionCount p.call.identity p.slot := by
  have reads := checked.2.2.2.2.2.2.2.2.2
  simpa only [ModeReads, mode] using reads

omit [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact] in
/-- Complete passive receipt membership is a query requirement, not a solver
success precondition. All fields, including replay/incoming/cuts, are retained. -/
theorem forward_completed_drain (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (p : ForwardProbe Id Fact)
    (checked : ForwardReads e q index endpoint p) :
    e.receiptCandidates p.call.identity = [p.receipt] ∧
    e.completionCandidates p.call.identity = [{ p.receipt with completed := true }] ∧
    p.receipt.completed = false ∧ p.call.originCut ≤ p.receipt.originIndex ∧
    e.origins[p.receipt.originIndex]? = some ⟨p.receipt.createdSeed, p.call.occurrence, p.call.slot, p.receipt⟩ ∧
    p.receipt.selectedRelation = p.receipt.incomingRelation.getD p.receipt.createdSeed ∧
    p.receipt.selectedRelation ∈ e.after.current.liveRelations ∧
    e.after.current.relationPair p.receipt.selectedRelation = some p.receipt.task := by
  have d := checked.2.1
  exact ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1,
    d.2.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.2.2.2⟩

omit [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact] in
/-- Frame preservation checks actual initial/current native vectors, and so
includes pre-existing endpoints independently of which decisions suppress. -/
theorem frame_preserves_existing (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (checked : FrameReads e q) (atom : Id) (before : atom ∈ q.frame.before.lowerAtoms) :
    atom ∈ q.frame.after.lowerAtoms ∧ e.after.current.effectRows q.frame.row = some q.frame.after := by
  rcases checked with ⟨_, _, current, _, atoms, _, _⟩
  exact ⟨by rw [atoms]; exact List.mem_append_left _ before, current⟩

omit [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact] in
theorem frame_preserves_same_family_sibling (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (checked : FrameReads e q) (sibling : Id) (familyOf : Id → Option Id)
    (sameFamily : familyOf sibling = some q.context.query.family)
    (before : sibling ∈ q.frame.before.lowerAtoms) :
    familyOf sibling = some q.context.query.family ∧ sibling ∈ q.frame.after.lowerAtoms :=
  ⟨sameFamily, (frame_preserves_existing e q checked sibling before).1⟩

theorem absent_completion_unavailable (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (item : Item Id Fact) (p : ForwardProbe Id Fact) (member : item ∈ q.items)
    (decision : item.decision = .forward) (probe : item.probe = .forwarded p)
    (missing : e.completionCandidates p.call.identity = []) : observe e q = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have checked := accepted_item e q accepted item member
  simp only [ItemReads, decision, probe] at checked
  have completion := checked.2.1.2.1
  rw [missing] at completion
  cases completion

theorem suppressed_emits_no_local_call (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (item : Item Id Fact) (member : item ∈ q.items)
    (decision : item.decision = .suppress) :
    item.probe = .suppressed ∧ e.callCandidates q.publication item.index = [] := by
  have checked := accepted_item e q accepted item member
  cases hp : item.probe with
  | suppressed => exact ⟨rfl, by simpa only [ItemReads, decision, hp] using checked⟩
  | forwarded p => simp [ItemReads, decision, hp] at checked

/-- Every original unmatched Forward is still present in the pure published
trace with multiplicity. Native existence additionally follows per checked Item. -/
theorem unmatched_trace_count (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (endpoint : Endpoint Id)
    (different : endpoint ≠ AuthenticatedResidualConsumerR49.target q.context) :
    (AuthenticatedResidualConsumerR49.fold q.originalFact.upper (itemPlan q.items)).count
      (endpoint, q.originalFact.upper) = q.original.count endpoint := by
  exact AuthenticatedResidualConsumerR49.unmatched_count _ _ _ (accepted_plan e q accepted).1 _ _ different

/-- Composition from the accepted R50 decision to the exact current native
result slot. Old bounds are permitted without inventing an emission. -/
theorem accepted_forward_native (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (item : Item Id Fact) (member : item ∈ q.items)
    (decision : item.decision = .forward) :
    ∃ p, item.probe = .forwarded p ∧ ForwardReads e q item.index item.endpoint p ∧
      currentBound e.after.current p.slot = some p.bound ∧ p.bound.item = item.endpoint ∧
      p.call.upper = q.originalFact.upper ∧ p.call.cause = q.originalFact.cause := by
  have checked := accepted_item e q accepted item member
  cases hp : item.probe with
  | suppressed => simp [ItemReads, decision, hp] at checked
  | forwarded p =>
    have reads : ForwardReads e q item.index item.endpoint p := by simpa only [ItemReads, decision, hp] using checked
    have current := forward_current_native e q item.index item.endpoint p reads
    have arguments := forward_exact_arguments e q item.index item.endpoint p reads
    exact ⟨p, rfl, reads, current.1, current.2.1, arguments.2.1, arguments.2.2.2.2.2.1⟩

/-- An original unmatched endpoint is not merely retained in a proposed fold:
accepted publication observations locate its exact current native result bound. -/
theorem original_unmatched_survives_native (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (endpoint : Endpoint Id) (member : endpoint ∈ q.original)
    (different : endpoint ≠ AuthenticatedResidualConsumerR49.target q.context) :
    ∃ item ∈ q.items, ∃ p, item.endpoint = endpoint ∧ item.decision = .forward ∧
      item.probe = .forwarded p ∧ currentBound e.after.current p.slot = some p.bound ∧
      p.bound.item = endpoint ∧ p.call.upper = q.originalFact.upper ∧ p.call.cause = q.originalFact.cause := by
  have plan := accepted_plan e q accepted
  have endpoints : q.items.map Item.endpoint = q.original := by
    simpa only [itemPlan, List.map_map, Function.comp_def] using plan.2
  have inItems : endpoint ∈ q.items.map Item.endpoint := by rw [endpoints]; exact member
  obtain ⟨item, itemMember, same⟩ := List.mem_map.mp inItems
  have decision := (AuthenticatedResidualConsumerR49.plan_correspondence _ _ _ plan.1).2
    item.endpoint item.decision (List.mem_map.mpr ⟨item, itemMember, rfl⟩)
  have forward : item.decision = .forward := by
    cases hd : item.decision with
    | forward => rfl
    | suppress =>
      have sameTarget := ((AuthenticatedResidualConsumerR49.suppression_iff _ _).mp (hd ▸ decision)).1
      exact False.elim (different (same.symm.trans sameTarget))
  obtain ⟨p, probe, _, current, itemBound, upper, cause⟩ := accepted_forward_native e q accepted item itemMember forward
  exact ⟨item, itemMember, p, same, forward, probe, current, itemBound.trans same, upper, cause⟩

def witnessFact : OriginalFact Nat Nat := ⟨300, 200, 51, 500, .effectRow 4, .effectRow 9⟩
def witnessBefore : RowBounds Nat := ⟨[], [], [8], []⟩
def witnessAfter : RowBounds Nat := ⟨[], [], [8, 7], []⟩
def witnessSlot : Slot Nat := ⟨.effect 9, .effectLowerAtom, 1⟩
def witnessOldSlot : Slot Nat := ⟨.effect 9, .effectLowerAtom, 0⟩
def witnessBound : Bound Nat := ⟨.effect 9, .positive, .effectAtom 7⟩
def witnessOldBound : Bound Nat := ⟨.effect 9, .positive, .effectAtom 8⟩
def witnessAdmission : Admission Nat := ⟨witnessBound, some 1⟩
def witnessEmission : Emission Nat := ⟨0, witnessBound, witnessSlot, ⟨witnessSlot, witnessBound⟩⟩
def witnessPhysical : CurrentEmissionOwnershipR47.Probe Nat :=
  ⟨0, 0, witnessAdmission, witnessEmission, 1, [1]⟩
def witnessCall : Call Nat Nat := ⟨0, 10, 0, .effectAtom 7, .effectRow 9, 300, 200, 51, 500, 0, 0, true⟩
def witnessOldCall : Call Nat Nat := ⟨1, 10, 1, .effectAtom 8, .effectRow 9, 300, 200, 51, 500, 1, 1, true⟩
def witnessDrain : Drain Nat := ⟨0, none, none, 0, 0, 0, (.effectAtom 7, .effectRow 9), 500, false⟩
def witnessOldDrain : Drain Nat := ⟨1, none, none, 2, 2, 1, (.effectAtom 8, .effectRow 9), 500, false⟩
def witnessForward : ForwardProbe Nat Nat :=
  ⟨witnessCall, witnessDrain, witnessSlot, witnessBound, some witnessPhysical, .newlyEmitted⟩
def witnessOldForward : ForwardProbe Nat Nat :=
  ⟨witnessOldCall, witnessOldDrain, witnessOldSlot, witnessOldBound, none, .alreadyPresent⟩
def witnessNative : CurrentEmissionOwnershipR47.Inputs Nat Nat Nat :=
  { CurrentEmissionOwnershipR47.witnessInputs with
    admissions := [witnessAdmission]
    emissions := [witnessEmission]
    effectRows := fun row => if row = 9 then some witnessAfter else none
    liveRelations := [0, 1, 2]
    dependencies := [(0, 1)]
    relationPair := fun relation => if relation = 0 ∨ relation = 1 then
      some (.effectAtom 7, .effectRow 9) else if relation = 2 then some (.effectAtom 8, .effectRow 9) else none }
def witnessInputs : Inputs Nat Nat Nat :=
  ⟨{ AuthenticatedResidualConsumerR49.witnessArrival with current := witnessNative },
    (fun fact => if fact = 300 then some witnessFact else none),
    (fun publication index => if publication = 10 ∧ index = 0 then [witnessCall] else
      if publication = 10 ∧ index = 1 then [witnessOldCall] else []),
    (fun identity => if identity = 0 then some witnessCall else if identity = 1 then some witnessOldCall else none),
    (fun identity => if identity = 0 then [witnessDrain] else if identity = 1 then [witnessOldDrain] else []),
    (fun identity => if identity = 0 then [{ witnessDrain with completed := true }] else
      if identity = 1 then [{ witnessOldDrain with completed := true }] else []),
    [⟨0, 200, 51, witnessDrain⟩, ⟨2, 200, 51, witnessOldDrain⟩],
    (fun upper => if upper = .effectRow 9 then some 9 else none),
    (fun identity slot => if identity = 1 ∧ slot = witnessOldSlot then some witnessOldBound else none),
    (fun identity slot => if identity = 0 ∧ slot = witnessSlot then [0] else []),
    (fun _ _ => 0),
    (fun row endpoint => if row = 9 ∧ endpoint = .effectAtom 7 then [witnessSlot] else
      if row = 9 ∧ endpoint = .effectAtom 8 then [witnessOldSlot] else []),
    (fun row => if row = 9 then some witnessBefore else none)⟩
def witnessQuery : Query Nat Nat Nat Nat :=
  ⟨AuthenticatedResidualConsumerR49.knownUnmatchedContext, 10, [.effectAtom 7, .effectAtom 8], witnessFact,
    ⟨9, witnessBefore, witnessAfter, [], [7]⟩,
    [⟨0, .effectAtom 7, .forward, .forwarded witnessForward⟩,
      ⟨1, .effectAtom 8, .forward, .forwarded witnessOldForward⟩]⟩

/-- Constructed finite observation, not a Rust execution receipt. It validates
both publication modes, including an old sibling with zero prior emissions. -/
theorem concrete_new_and_existing_publication :
    observe witnessInputs witnessQuery = true ∧
    ForwardReads witnessInputs witnessQuery 0 (.effectAtom 7) witnessForward ∧
    ForwardReads witnessInputs witnessQuery 1 (.effectAtom 8) witnessOldForward ∧
    witnessInputs.priorEmissionCount 1 witnessOldSlot = 0 ∧
    emissionsForSlot witnessInputs.after.current witnessOldSlot = [] ∧
    (7 ∈ witnessQuery.frame.after.lowerAtoms) ∧ (8 ∈ witnessQuery.frame.after.lowerAtoms) := by decide

/-- The call can have returned while passive completion observation was lost;
this affects only observation availability in this finite model. -/
theorem concrete_completion_loss_is_observation_gap :
    witnessCall.returned = true ∧
    witnessOldCall.returned = true ∧
    observe { witnessInputs with completionCandidates := fun _ => [] } witnessQuery = false := by decide

/-- Pre-existing target and same-family sibling survive a suppressed decision.
Suppression asserts no local forward call, not global native target absence. -/
def suppressionQuery : Query Nat Nat Nat Nat :=
  { witnessQuery with
    context := AuthenticatedResidualConsumerR49.witnessContext
    original := [.effectAtom 7]
    frame := ⟨9, ⟨[], [], [7, 8], []⟩, ⟨[], [], [7, 8], []⟩, [], []⟩
    items := [⟨0, .effectAtom 7, .suppress, .suppressed⟩] }
def suppressionInputs : Inputs Nat Nat Nat :=
  { witnessInputs with
    after := { witnessInputs.after with current := { witnessNative with
      admissions := []
      emissions := []
      effectRows := fun row => if row = 9 then some suppressionQuery.frame.after else none } }
    initialRows := fun row => if row = 9 then some suppressionQuery.frame.before else none
    callCandidates := fun _ _ => [] }

theorem concrete_suppression_is_not_global_absence :
    observe suppressionInputs suppressionQuery = true ∧
    suppressionInputs.callCandidates 10 0 = [] ∧
    suppressionInputs.after.current.effectRows 9 = some suppressionQuery.frame.after ∧
    7 ∈ suppressionQuery.frame.after.lowerAtoms ∧ 8 ∈ suppressionQuery.frame.after.lowerAtoms := by decide

/-- Wrong source arguments, missing/ambiguous attribution, stale native reads,
misclassified pre-existing evidence and lost sibling frames reject observation. -/
theorem concrete_bad_publication_observations_rejected :
    observe { witnessInputs with calls := fun _ => none } witnessQuery = false ∧
    observe { witnessInputs with boundCandidates := fun _ _ => [witnessSlot, witnessSlot] } witnessQuery = false ∧
    observe { witnessInputs with receiptCandidates := fun _ => [] } witnessQuery = false ∧
    observe { witnessInputs with receiptCandidates := fun _ => [witnessDrain, witnessDrain] } witnessQuery = false ∧
    observe { witnessInputs with after := { witnessInputs.after with current := { witnessNative with
      effectRows := fun _ => none } } } witnessQuery = false ∧
    observe witnessInputs { witnessQuery with items :=
      [⟨0, .effectAtom 7, .forward, .forwarded { witnessForward with call := { witnessCall with cause := 501 } }⟩,
        ⟨1, .effectAtom 8, .forward, .forwarded witnessOldForward⟩] } = false ∧
    observe witnessInputs { witnessQuery with items :=
      [⟨0, .effectAtom 7, .forward, .forwarded { witnessForward with call := { witnessCall with upper := .effectRow 10 } }⟩,
        ⟨1, .effectAtom 8, .forward, .forwarded witnessOldForward⟩] } = false ∧
    observe witnessInputs { witnessQuery with items :=
      [⟨0, .effectAtom 7, .forward, .forwarded witnessForward⟩,
        ⟨1, .effectAtom 8, .forward, .forwarded { witnessOldForward with mode := .newlyEmitted }⟩] } = false ∧
    observe witnessInputs { witnessQuery with frame := { witnessQuery.frame with atomsSuffix := [] } } = false := by decide

/-- Constructive finite-list proof, avoiding the classical simp-decision
proof used by the standard range Nodup theorem. -/
theorem map_succ_nodup (xs : List Nat) (nodup : xs.Nodup) : (xs.map Nat.succ).Nodup := by
  change List.Pairwise (fun a b => a ≠ b) xs at nodup
  change List.Pairwise (fun a b => a ≠ b) (xs.map Nat.succ)
  induction nodup with
  | nil => exact .nil
  | @cons head rest separate _ ih =>
    apply List.Pairwise.cons
    · intro value member equal
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact separate original originalMember (Nat.succ.inj equal)
    · exact ih

theorem range_nodup_constructive (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [List.range_succ_eq_map]
    apply List.Pairwise.cons
    · intro value member equal
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      exact Nat.noConfusion equal
    · exact map_succ_nodup _ ih

/-- Complete ordered item indices rule out aliasing decisions by endpoint. -/
theorem accepted_index_order (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) :
    q.items.map Item.index = List.range q.items.length ∧ (q.items.map Item.index).Nodup := by
  have h : Reads e q := of_decide_eq_true accepted
  exact ⟨h.2.1, by rw [h.2.1]; exact range_nodup_constructive _⟩

theorem accepted_item_at_index (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (item : Item Id Fact) (member : item ∈ q.items) :
    q.items[item.index]? = some item := by
  obtain ⟨position, atPosition⟩ := List.mem_iff_getElem?.mp member
  have bound : position < q.items.length := (List.getElem?_eq_some_iff.mp atPosition).1
  have indices := (accepted_index_order e q accepted).1
  have atIndex := congrArg (fun values : List Nat => values[position]?) indices
  have equal : item.index = position := by
    simpa only [List.getElem?_map, atPosition, Option.map_some, List.getElem?_range bound, Option.some.injEq] using atIndex
  rw [equal]; exact atPosition

theorem accepted_index_unique (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) (first second : Item Id Fact)
    (firstMember : first ∈ q.items) (secondMember : second ∈ q.items)
    (sameIndex : first.index = second.index) : first = second := by
  have a := accepted_item_at_index e q accepted first firstMember
  have b := accepted_item_at_index e q accepted second secondMember
  rw [sameIndex] at a
  exact Option.some.inj (a.symm.trans b)

/-- The native result list equals the retained initial frame followed by
precisely the plan's observed new Forward operands, in plan order. -/
theorem accepted_exact_native_frame (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (accepted : observe e q = true) :
    e.initialRows q.frame.row = some q.frame.before ∧
    e.after.current.effectRows q.frame.row = some q.frame.after ∧
    q.frame.after.lowerRows = q.frame.before.lowerRows ++ plannedRows q.items ∧
    q.frame.after.lowerAtoms = q.frame.before.lowerAtoms ++ plannedAtoms q.items := by
  have h : Reads e q := of_decide_eq_true accepted
  rcases h.2.2.2.2.1 with ⟨_, before, after, rows, atoms, rowsPlan, atomsPlan⟩
  exact ⟨before, after, by simpa only [rowsPlan] using rows, by simpa only [atomsPlan] using atoms⟩

end YulangClosure.NativeResidualPublicationR51
