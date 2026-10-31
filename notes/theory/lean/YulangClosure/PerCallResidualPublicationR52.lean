import YulangClosure.NativeResidualPublicationR51

/-!
R52 conditional per-call extraction bridge. A key-indexed retained record
constructs R51's observation tables; native/source reads remain explicit.
This does not establish Rust extraction, successful inference, source typing,
A/B, or production authority. End cuts are exclusive, pre-call cuts inclusive.
-/
namespace YulangClosure.PerCallResidualPublicationR52

open CurrentEmissionOwnershipR47 (Endpoint Bound emissionsForSlot ancestryCheck currentBound)
open NativeResidualPublicationR51

structure Captured (Id Fact : Type) where
  probe : ForwardProbe Id Fact
  originEnd : Nat
  emissionEnd : Nat
  completion : Option (Drain Id)
  before : Option (Bound Id)
  emitted : List Nat
  priorCount : Nat
  completionCut : Nat
  completionEnd : Nat
  completionIndex : Nat

/-- Publication/index is the primary lookup, before any endpoint comparison.
The identity index must return the SAME record, not a matching task record. -/
structure Store (Id Fact : Type) where
  keyed : Nat → Nat → Option (Captured Id Fact)
  identified : Nat → Option (Captured Id Fact)

variable {Artifact Id Term Fact : Type}

def Installed (s : Store Id Fact) (r : Captured Id Fact) : Prop :=
  s.keyed r.probe.call.publication r.probe.call.planIndex = some r ∧
  s.identified r.probe.call.identity = some r

def Window (cut finish index : Nat) : Prop := cut ≤ index ∧ index < finish

instance (cut finish index : Nat) : Decidable (Window cut finish index) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Only tables supplied by per-call capture are replaced. Native state,
source facts, current slots and publication frame are still the original reads. -/
def project [DecidableEq Id] (base : Inputs Artifact Id Fact) (s : Store Id Fact) : Inputs Artifact Id Fact :=
  { base with
    callCandidates := fun publication index => ((s.keyed publication index).toList).map (·.probe.call)
    calls := fun identity => (s.identified identity).map (·.probe.call)
    receiptCandidates := fun identity => ((s.identified identity).toList).map (·.probe.receipt)
    completionCandidates := fun identity => match s.identified identity with
      | none => []
      | some r => r.completion.toList
    beforeBound := fun identity slot => match s.identified identity with
      | none => none
      | some r => if slot = r.probe.slot then r.before else none
    newEmissions := fun identity slot => match s.identified identity with
      | none => []
      | some r => if slot = r.probe.slot then r.emitted else []
    priorEmissionCount := fun identity slot => match s.identified identity with
      | none => 0
      | some r => if slot = r.probe.slot then r.priorCount else 0 }

/-- Exact original argument/owner reads, independent of registry lookup. -/
def CallSource (q : Query Artifact Id Term Fact) (index : Nat) (endpoint : Endpoint Id)
    (r : Captured Id Fact) : Prop :=
  r.probe.call.publication = q.publication ∧ r.probe.call.planIndex = index ∧
  r.probe.call.endpoint = endpoint ∧ r.probe.call.upper = q.originalFact.upper ∧
  r.probe.call.fact = q.originalFact.fact ∧ r.probe.call.occurrence = q.originalFact.occurrence ∧
  r.probe.call.slot = q.originalFact.slot ∧ r.probe.call.cause = q.originalFact.cause ∧
  r.probe.call.returned = true

/-- Complete origin, receipt and completion are retained from this call's
half-open segment. This premise must be supplied by the actual producer. -/
def DrainSource (base : Inputs Artifact Id Fact) (r : Captured Id Fact) : Prop :=
  r.completion = some { r.probe.receipt with completed := true } ∧
  r.probe.receipt.completed = false ∧
  Window r.completionCut r.completionEnd r.completionIndex ∧
  Window r.probe.call.originCut r.originEnd r.probe.receipt.originIndex ∧
  base.origins[r.probe.receipt.originIndex]? =
    some ⟨r.probe.receipt.createdSeed, r.probe.call.occurrence, r.probe.call.slot, r.probe.receipt⟩ ∧
  r.probe.receipt.task = (r.probe.call.endpoint, r.probe.call.upper) ∧
  r.probe.receipt.cause = r.probe.call.cause ∧
  r.probe.receipt.selectedRelation = r.probe.receipt.incomingRelation.getD r.probe.receipt.createdSeed ∧
  r.probe.receipt.createdSeed ∈ base.after.current.liveRelations ∧
  r.probe.receipt.selectedRelation ∈ base.after.current.liveRelations ∧
  base.after.current.relationPair r.probe.receipt.selectedRelation = some r.probe.receipt.task

/-- Snapshot values and native physical reads, with no old emission required
for AlreadyPresent. R51's lower cut is strengthened by the same call's end. -/
def ModeSource [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) (r : Captured Id Fact) : Prop :=
  match r.probe.mode with
  | .newlyEmitted =>
      ∃ physical ∈ r.probe.physical.toList,
        physical.emission.physical = r.probe.slot ∧ physical.admission.bound = r.probe.bound ∧
        ProviderEntryArrivalR48.EdgeReads base.after (.effectRow q.frame.row) physical ∧
        r.before = none ∧ r.emitted = [physical.emissionIndex] ∧ r.priorCount = 0 ∧
        Window r.probe.call.emissionCut r.emissionEnd physical.emissionIndex ∧
        ancestryCheck base.after.current r.probe.receipt.selectedRelation physical.ancestry physical.relation = true
  | .alreadyPresent =>
      r.probe.physical = none ∧ r.before = some r.probe.bound ∧ r.emitted = [] ∧
      (emissionsForSlot base.after.current r.probe.slot).length = r.priorCount

theorem key_unique (s : Store Id Fact) (publication index : Nat) (a b : Captured Id Fact)
    (ha : s.keyed publication index = some a) (hb : s.keyed publication index = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

theorem identity_unique (s : Store Id Fact) (a b : Captured Id Fact)
    (ha : Installed s a) (hb : Installed s b) (same : a.probe.call.identity = b.probe.call.identity) : a = b := by
  have h := ha.2
  rw [same] at h
  exact Option.some.inj (h.symm.trans hb.2)

theorem distinct_keys_no_alias (a b : Captured Id Fact)
    (different : (a.probe.call.publication, a.probe.call.planIndex) ≠
      (b.probe.call.publication, b.probe.call.planIndex)) : a ≠ b := by
  intro equal
  exact different (congrArg (fun r : Captured Id Fact => (r.probe.call.publication, r.probe.call.planIndex)) equal)

theorem window_disjoint (cutA endA cutB endB index : Nat)
    (order : endA ≤ cutB) (first : Window cutA endA index) : ¬ Window cutB endB index := by
  intro second
  exact Nat.not_lt_of_ge second.1 (Nat.lt_of_lt_of_le first.2 order)

theorem earlier_rejected (cut finish index : Nat) (earlier : index < cut) : ¬ Window cut finish index := by
  intro h
  exact Nat.not_lt_of_ge h.1 earlier

theorem later_rejected (cut finish index : Nat) (later : finish ≤ index) : ¬ Window cut finish index := by
  intro h
  exact Nat.not_lt_of_ge later h.2

theorem lower_cut_inclusive (cut finish : Nat) : Window cut finish cut ↔ cut < finish :=
  ⟨fun h => h.2, fun h => ⟨Nat.le_refl _, h⟩⟩

theorem upper_cut_exclusive (cut finish : Nat) : ¬ Window cut finish finish :=
  later_rejected cut finish finish (Nat.le_refl _)

theorem origin_separation (base : Inputs Artifact Id Fact) (a b : Captured Id Fact)
    (ha : DrainSource base a) (hb : DrainSource base b)
    (order : a.originEnd ≤ b.probe.call.originCut) : a.probe.receipt.originIndex ≠ b.probe.receipt.originIndex := by
  intro same
  have first := ha.2.2.2.1
  rw [same] at first
  exact window_disjoint _ _ _ _ _ order first hb.2.2.2.1

theorem completion_separation (base : Inputs Artifact Id Fact) (a b : Captured Id Fact)
    (ha : DrainSource base a) (hb : DrainSource base b)
    (order : a.completionEnd ≤ b.completionCut) : a.completionIndex ≠ b.completionIndex := by
  intro same
  have first := ha.2.2.1
  rw [same] at first
  exact window_disjoint _ _ _ _ _ order first hb.2.2.1

/-- Ordered call emission segments cannot share an emission index, even if
all source task/occurrence/cause fields compare equal. -/
theorem emission_separation (a b : Captured Id Fact) (first second : Nat)
    (ha : Window a.probe.call.emissionCut a.emissionEnd first)
    (hb : Window b.probe.call.emissionCut b.emissionEnd second)
    (order : a.emissionEnd ≤ b.probe.call.emissionCut) : first ≠ second := by
  intro same
  rw [same] at ha
  exact window_disjoint _ _ _ _ _ order ha hb

/-- R51 call identity and checked original plan index cannot be swapped. -/
theorem call_identity_fixes_index (e : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (first second : Nat) (x y : Endpoint Id) (p t : ForwardProbe Id Fact)
    (hp : CallReads e q first x p) (ht : CallReads e q second y t)
    (same : p.call.identity = t.call.identity) : first = second := by
  have read := hp.2.1
  rw [same] at read
  have equal : p.call = t.call := Option.some.inj (read.symm.trans ht.2.1)
  exact hp.2.2.2.1.symm.trans ((congrArg Call.planIndex equal).trans ht.2.2.2.1)

/-- One retained record supplies all THREE R51 interfaces. The construction
supplies candidate tables; the premises expose the still-open source reads. -/
theorem captured_instantiates_r51 [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (r : Captured Id Fact)
    (installed : Installed s r) (call : CallSource q index endpoint r)
    (drain : DrainSource base r) (mode : ModeSource base q r) :
    CallReads (project base s) q index endpoint r.probe ∧
    DrainReads (project base s) r.probe ∧ ModeReads (project base s) q r.probe := by
  rcases call with ⟨pub, idx, endpointRead, upper, fact, occurrence, slot, cause, returned⟩
  rcases drain with ⟨completion, incomplete, _completionWindow, window, origin, task, drainCause, selected, createdLive, selectedLive, pair⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by simp [project, ← pub, ← idx, installed.1], by simp [project, installed.2],
      pub, idx, endpointRead, upper, fact, occurrence, slot, cause, returned⟩
  · exact ⟨by simp [project, installed.2], by simp [project, installed.2, completion],
      incomplete, window.1, origin, task, drainCause, selected, createdLive, selectedLive, pair⟩
  · cases hm : r.probe.mode with
    | newlyEmitted =>
      simp only [ModeSource, hm] at mode
      simp only [ModeReads, hm]
      obtain ⟨physical, member, physicalSlot, physicalBound, edge, before, emitted, prior, cuts, path⟩ := mode
      exact ⟨physical, member, physicalSlot, physicalBound, edge,
        by simp [project, installed.2, before], by simp [project, installed.2, emitted],
        by simp [project, installed.2, prior], cuts.1, path⟩
    | alreadyPresent =>
      simp only [ModeSource, hm] at mode
      simp only [ModeReads, hm]
      rcases mode with ⟨physical, before, emitted, count⟩
      exact ⟨physical, by simp [project, installed.2, before],
        by simp [project, installed.2, emitted], by simpa [project, installed.2] using count⟩

/-- Direct application at R51's source-correspondence seam. The SAME captured
probe is passed through R51's native-current theorem; no replacement witness. -/
theorem captured_forward_native [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (r : Captured Id Fact)
    (installed : Installed s r) (call : CallSource q index endpoint r)
    (drain : DrainSource base r) (mode : ModeSource base q r)
    (native : base.boundCandidates q.frame.row endpoint = [r.probe.slot] ∧
      currentBound base.after.current r.probe.slot = some r.probe.bound ∧
      r.probe.bound.owner = .effect q.frame.row ∧ r.probe.slot.owner = .effect q.frame.row ∧
      r.probe.bound.item = endpoint ∧ r.probe.bound.polarity = .positive ∧
      (r.probe.slot.lane = .effectLowerRow ∨ r.probe.slot.lane = .effectLowerAtom)) :
    ForwardReads (project base s) q index endpoint r.probe ∧
    currentBound base.after.current r.probe.slot = some r.probe.bound ∧ r.probe.bound.item = endpoint := by
  obtain ⟨hc, hd, hm⟩ := captured_instantiates_r51 base s q index endpoint r installed call drain mode
  rcases native with ⟨candidates, current, owner, slotOwner, item, polarity, lane⟩
  have checked : ForwardReads (project base s) q index endpoint r.probe :=
    ⟨hc, hd, candidates, current, owner, slotOwner, item, polarity, lane, hm⟩
  have result := forward_current_native (project base s) q index endpoint r.probe checked
  exact ⟨checked, result.1, result.2.1⟩

theorem captured_missing_completion_unavailable [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (item : Item Id Fact) (r : Captured Id Fact) (installed : Installed s r)
    (member : item ∈ q.items) (decision : item.decision = .forward)
    (probe : item.probe = .forwarded r.probe) (missing : r.completion = none)
    (returned : r.probe.call.returned = true) :
    r.probe.call.returned = true ∧ observe (project base s) q = false := by
  refine ⟨returned, absent_completion_unavailable _ q item r.probe member decision probe ?_⟩
  simp [project, installed.2, missing]

/-- The source-mode premise itself rejects a neighboring later emission,
independently of whether other native physical checks happen to succeed. -/
theorem later_emission_source_rejected [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact) (r : Captured Id Fact)
    (physical : CurrentEmissionOwnershipR47.Probe Id)
    (mode : r.probe.mode = .newlyEmitted) (same : r.probe.physical = some physical)
    (later : r.emissionEnd ≤ physical.emissionIndex) : ¬ ModeSource base q r := by
  intro source
  simp only [ModeSource, mode, same, Option.toList_some, List.mem_singleton] at source
  obtain ⟨selected, equal, _, _, _, _, _, _, window, _⟩ := source
  subst selected
  exact later_rejected _ _ _ later window

/-- Missing observer storage cannot change a successful call's returned field.
This is a finite model separation, not Rust execution or allocation evidence. -/
theorem unavailable_observer_successful_forward [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (item : Item Id Fact) (p : ForwardProbe Id Fact) (member : item ∈ q.items)
    (decision : item.decision = .forward) (probe : item.probe = .forwarded p)
    (returned : p.call.returned = true) :
    p.call.returned = true ∧
    observe (project base ⟨fun _ _ => none, fun _ => none⟩) q = false := by
  exact ⟨returned, absent_completion_unavailable _ q item p member decision probe rfl⟩

def witnessNew : Captured Nat Nat :=
  ⟨witnessForward, 1, 1, some { witnessDrain with completed := true }, none, [0], 0, 0, 1, 0⟩
def witnessOld : Captured Nat Nat :=
  ⟨witnessOldForward, 2, 1, some { witnessOldDrain with completed := true }, some witnessOldBound, [], 0, 1, 2, 1⟩
def witnessStore : Store Nat Nat :=
  ⟨(fun publication index => if publication = 10 ∧ index = 0 then some witnessNew else
      if publication = 10 ∧ index = 1 then some witnessOld else none),
    (fun identity => if identity = 0 then some witnessNew else if identity = 1 then some witnessOld else none)⟩

/-- Two genuinely equal task/occurrence/cause records still have distinct keys
and origin intervals. No task/occurrence/cause query is used by project. -/
def repeatedCall : Captured Nat Nat :=
  { witnessNew with
    probe := { witnessForward with
      call := { witnessCall with identity := 2, planIndex := 2, originCut := 2, emissionCut := 1 }
      receipt := { witnessDrain with drainIndex := 2, createdSeed := 3, selectedRelation := 3, originIndex := 2 }
      physical := none
      mode := .alreadyPresent }
    originEnd := 3
    emissionEnd := 1
    completion := some { witnessDrain with
      drainIndex := 2
      createdSeed := 3
      selectedRelation := 3
      originIndex := 2
      completed := true }
    before := some witnessBound
    emitted := []
    priorCount := 1
    completionCut := 2
    completionEnd := 3
    completionIndex := 2 }

theorem concrete_repeated_calls_distinct :
    witnessNew.probe.call.occurrence = repeatedCall.probe.call.occurrence ∧
    witnessNew.probe.receipt.task = repeatedCall.probe.receipt.task ∧
    witnessNew.probe.call.cause = repeatedCall.probe.call.cause ∧
    witnessNew.probe.call.identity ≠ repeatedCall.probe.call.identity ∧
    witnessNew.probe.call.planIndex ≠ repeatedCall.probe.call.planIndex ∧
    witnessNew.originEnd ≤ repeatedCall.probe.call.originCut := by decide

/-- Constructed finite positive instances for both modes, including zero old
emissions. These are not claimed to have been extracted from a Rust run. -/
theorem concrete_same_record_bridge :
    CallReads (project witnessInputs witnessStore) witnessQuery 0 (.effectAtom 7) witnessNew.probe ∧
    DrainReads (project witnessInputs witnessStore) witnessNew.probe ∧
    ModeReads (project witnessInputs witnessStore) witnessQuery witnessNew.probe ∧
    CallReads (project witnessInputs witnessStore) witnessQuery 1 (.effectAtom 8) witnessOld.probe ∧
    DrainReads (project witnessInputs witnessStore) witnessOld.probe ∧
    ModeReads (project witnessInputs witnessStore) witnessQuery witnessOld.probe ∧
    witnessOld.priorCount = 0 ∧ emissionsForSlot witnessInputs.after.current witnessOld.probe.slot = [] := by decide

theorem concrete_source_premises :
    Installed witnessStore witnessNew ∧
    CallSource witnessQuery 0 (.effectAtom 7) witnessNew ∧
    DrainSource witnessInputs witnessNew ∧ ModeSource witnessInputs witnessQuery witnessNew := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · unfold CallSource; decide
  · unfold DrainSource Window; decide
  · simp only [ModeSource, witnessNew, witnessForward]; unfold Window; decide

theorem concrete_parent_application :
    CallReads (project witnessInputs witnessStore) witnessQuery 0 (.effectAtom 7) witnessNew.probe ∧
    DrainReads (project witnessInputs witnessStore) witnessNew.probe ∧
    ModeReads (project witnessInputs witnessStore) witnessQuery witnessNew.probe :=
  captured_instantiates_r51 witnessInputs witnessStore witnessQuery 0 (.effectAtom 7) witnessNew
    concrete_source_premises.1 concrete_source_premises.2.1
    concrete_source_premises.2.2.1 concrete_source_premises.2.2.2

def repeatedInputs : Inputs Nat Nat Nat :=
  { witnessInputs with
    origins := witnessInputs.origins ++ [⟨3, 200, 51, repeatedCall.probe.receipt⟩]
    after := { witnessInputs.after with current := { witnessNative with
      liveRelations := [0, 1, 2, 3]
      relationPair := fun relation => if relation = 3 then some (.effectAtom 7, .effectRow 9)
        else witnessNative.relationPair relation } } }
def repeatedStore : Store Nat Nat :=
  { witnessStore with
    keyed := fun publication index => if publication = 10 ∧ index = 2 then some repeatedCall
      else witnessStore.keyed publication index
    identified := fun identity => if identity = 2 then some repeatedCall else witnessStore.identified identity }
def repeatedQuery : Query Nat Nat Nat Nat :=
  { witnessQuery with
    original := [.effectAtom 7, .effectAtom 8, .effectAtom 7]
    items := witnessQuery.items ++ [⟨2, .effectAtom 7, .forward, .forwarded repeatedCall.probe⟩] }

/-- Repeated equal source calls are separately accepted at their original
indices; swapping their records rejects observation. -/
theorem concrete_repeated_publication :
    observe (project repeatedInputs repeatedStore) repeatedQuery = true ∧
    CallReads (project repeatedInputs repeatedStore) repeatedQuery 0 (.effectAtom 7) witnessNew.probe ∧
    CallReads (project repeatedInputs repeatedStore) repeatedQuery 2 (.effectAtom 7) repeatedCall.probe ∧
    ¬ CallReads (project repeatedInputs repeatedStore) repeatedQuery 0 (.effectAtom 7) repeatedCall.probe ∧
    ¬ CallReads (project repeatedInputs repeatedStore) repeatedQuery 2 (.effectAtom 7) witnessNew.probe ∧
    ¬ DrainReads (project repeatedInputs repeatedStore)
      { repeatedCall.probe with receipt := witnessNew.probe.receipt } := by decide

theorem concrete_key_and_cut_attacks :
    ¬ CallReads (project witnessInputs witnessStore) witnessQuery 1 (.effectAtom 7) witnessNew.probe ∧
    ¬ CallReads (project witnessInputs witnessStore) { witnessQuery with publication := 11 }
      0 (.effectAtom 7) witnessNew.probe ∧
    ¬ DrainReads (project witnessInputs witnessStore)
      { witnessOldForward with receipt := witnessDrain } ∧
    ¬ Window witnessOld.completionCut witnessOld.completionEnd witnessNew.completionIndex ∧
    ¬ Window witnessNew.completionCut witnessNew.completionEnd witnessOld.completionIndex ∧
    ¬ Window witnessOld.probe.call.originCut witnessOld.originEnd witnessNew.probe.receipt.originIndex ∧
    ¬ Window witnessNew.probe.call.emissionCut witnessNew.emissionEnd 1 ∧
    Window witnessNew.probe.call.originCut witnessNew.originEnd 0 ∧
    ¬ Window witnessNew.probe.call.originCut witnessNew.originEnd 1 ∧
    ¬ Window (witnessNew.probe.call.originCut + 1) witnessNew.originEnd 0 ∧
    ¬ Window (witnessNew.probe.call.emissionCut + 1) witnessNew.emissionEnd 0 := by decide

def missingCompletionStore : Store Nat Nat :=
  { witnessStore with
    keyed := fun publication index => if publication = 10 ∧ index = 0 then
      some { witnessNew with completion := none } else witnessStore.keyed publication index
    identified := fun identity => if identity = 0 then some { witnessNew with completion := none }
      else witnessStore.identified identity }

theorem concrete_completion_gap_keeps_call :
    witnessNew.probe.call.returned = true ∧
    CallReads (project witnessInputs missingCompletionStore) witnessQuery 0 (.effectAtom 7) witnessNew.probe ∧
    observe (project witnessInputs missingCompletionStore) witnessQuery = false := by decide

theorem concrete_observer_loss_preserves_return :
    witnessNew.probe.call.returned = true ∧
    observe (project witnessInputs ⟨fun _ _ => none, fun _ => none⟩) witnessQuery = false := by decide

end YulangClosure.PerCallResidualPublicationR52
