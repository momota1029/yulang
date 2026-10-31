import YulangClosure.BoundedAncestryR61

/-! R62: computed owner-local Internal policy, split before ancestry.
This is a finite inventory reader. Rust inventory extraction, pointer branding,
resource schedules and the outer successful Run remain explicit obligations. -/
namespace YulangClosure.InternalRootPolicyR62
open ProviderNativeContextR57 ReachedSlotSearchR58

variable {S T : Type} [DecidableEq S] [DecidableEq T]
abbrev Source (S T : Type) := SourceInternalContextR55.Native Nat (Key S T) T Fact
abbrev Request (S T : Type) := InternalPermissionIncidenceR45.Query Nat (Key S T)

/-- Select by registration owner and recipe component before testing native
Function/entry equality. A missing/duplicate recipe for an eligible constructor
fails the entire selection, as in the native loop. -/
def ownerSelection (s : Source S T) (target : Key S T) (component : Nat) :
    Option (SourceInternalContextR55.Construction (Key S T) T) := do
  let choices ← s.constructions.mapM fun c =>
    match s.formals[c.registration]? with
    | none => some none
    | some f => if f.role = .computation ∧ f.owner = target then do
        let recipe ← SourceInternalContextR55.unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes
        some (if recipe.rootComponent = component then some c else none)
      else some none
  match choices.filterMap id with
  | [c] => some c
  | _ => none

/-- The probe is assembled from indexed/unique reads, never supplied by a
caller. R45's exact OwnerReads and Identity are checked in the next stage. -/
def sourceProbe (s : Source S T) (q : Request S T) : Option (InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact) := do
  let e := SourceInternalContextR55.internalInputs s
  let plan ← e.plan q.use
  let selected ← ownerSelection s q.targetOwner plan.targetRootComponent
  if selected.registration ≠ q.registration then none else do
    let (formal,root) ← e.formals q.registration
    let construction ← SourceInternalContextR55.unique (fun c => c.registration == q.registration) e.constructions
    let permission ← SourceInternalContextR55.unique (fun p => p.registration == q.registration) e.permissions
    let receipt ← SourceInternalContextR55.unique (fun r => r.use == q.use) e.receipts
    let fact ← receipt.fact
    let (_,component) ← e.lambdaRecipe q.lambda
    let child ← e.positiveFunctionChild construction.function
    some ⟨formal,root,component,construction,permission,plan,receipt,fact,child⟩

structure Incidence (s : Source S T) (q : Request S T) where
  probe : InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact
  read : sourceProbe s q = some probe
  owners : InternalPermissionIncidenceR45.OwnerReads (SourceInternalContextR55.internalInputs s) q probe
  identity : InternalPermissionIncidenceR45.Identity (SourceInternalContextR55.internalInputs s) q probe
  parameterRecipe : s.parameterRecipes[probe.formal.recipe]? = some probe.formal.parameter

def incidence (s : Source S T) (q : Request S T) : Except Failure (Incidence s q) :=
  match read : sourceProbe s q with
  | none => .error (nativeFailure .firstEntry .missingInternal)
  | some probe => if checked : InternalPermissionIncidenceR45.OwnerReads (SourceInternalContextR55.internalInputs s) q probe ∧
      InternalPermissionIncidenceR45.Identity (SourceInternalContextR55.internalInputs s) q probe ∧
      s.parameterRecipes[probe.formal.recipe]? = some probe.formal.parameter then
        .ok ⟨probe,read,checked.1,checked.2.1,checked.2.2⟩
    else .error (nativeFailure .firstEntry .missingInternal)

def rootQuery (_n : Native S T) (q : Request S T) (i : Incidence s q) (root : Nat) :
    CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact := ⟨q.use,i.probe.fact,i.probe.permission.entry,root⟩

/-- Exactly R47 Matches with the ancestry conjunct removed. Ancestry is run
only after this certificate exists; it cannot be used to choose a source root. -/
def BeforeAncestry (n : Native S T) (q : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact)
    (p : CurrentEmissionOwnershipR47.Probe (Key S T)) : Prop :=
  (current n).admissions[p.admissionIndex]? = some p.admission ∧
  (current n).emissions[p.emissionIndex]? = some p.emission ∧
  p.emission.admission = p.admissionIndex ∧
  CurrentEmissionOwnershipR47.emissionsForSlot (current n) p.emission.physical = [p.emission] ∧
  p.emission.bound = p.admission.bound ∧ p.emission.readback.slot = p.emission.physical ∧
  p.emission.readback.bound = p.admission.bound ∧
  CurrentEmissionOwnershipR47.currentBound (current n) p.emission.physical = some p.admission.bound ∧
  p.admission.relation = some p.relation ∧
  (current n).relationPair p.relation = some (CurrentEmissionOwnershipR47.boundPair p.admission.bound) ∧
  CurrentEmissionOwnershipR47.RootMatches (current n) q ∧
  p.emission.physical.owner = .effect q.rawEntry ∧
  p.admission.bound.owner = .effect q.rawEntry ∧ p.admission.bound.polarity = .positive

instance (n : Native S T) (q : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact) (p : CurrentEmissionOwnershipR47.Probe (Key S T)) :
    Decidable (BeforeAncestry n q p) := by unfold BeforeAncestry; infer_instance

structure Root (s : Source S T) (n : Native S T) (q : Request S T) where
  incidence : Incidence s q
  sameArtifact : s.artifact = n.artifact
  entry : incidence.probe.permission.entry = .effectRow n.state n.entryRow
  value : Physical T
  root : Nat
  checked : BeforeAncestry n (rootQuery n q incidence root) (physical value)

/-- Source incidence first; then the selected native emission/current slot,
indexed admission/relation and unique source drain. No ancestry is evaluated. -/
def readRoot (s : Source S T) (n : Native S T) (q : Request S T) (index : Nat) :
    Except Failure (Root s n q) := do
  let i ← incidence s q
  if same : s.artifact = n.artifact then
    if entry : i.probe.permission.entry = .effectRow n.state n.entryRow then
      match n.emissions[index]? with
      | none => .error (nativeFailure .firstEntry .missingEmission)
      | some e =>
        if e.physical.owner = .effect n.entryRow ∧
            (e.physical.lane = .effectLowerRow ∨ e.physical.lane = .effectLowerAtom) then
          match CurrentEmissionOwnershipR47.currentBound (current n) (emission e).physical with
          | none => .error (nativeFailure .firstEntry .boundMismatch)
          | some fresh => match n.admissions[e.admission]? with
            | none => .error (nativeFailure .firstEntry .missingAdmission)
            | some a =>
              if (emission (S := S) e).bound = (admission a).bound ∧
                  (emission (S := S) e).bound = (emission e).readback.bound ∧
                  (emission (S := S) e).physical = (emission e).readback.slot ∧
                  (emission (S := S) e).bound = fresh then
                if CurrentEmissionOwnershipR47.emissionsForSlot (current n) (emission e).physical = [emission e] then
                  match a.relation with
                  | none => .error (nativeFailure .firstEntry .missingRelation)
                  | some relation =>
                    if (current n).relationPair relation = some (CurrentEmissionOwnershipR47.boundPair (admission a).bound) then
                      match (current n).rootCandidates q.use i.probe.fact with
                      | [root] =>
                        let value : Physical T := ⟨e.admission,index,a,e,relation,[]⟩
                        if checked : BeforeAncestry n (rootQuery n q i root) (physical value) then
                          .ok ⟨i,same,entry,value,root,checked⟩
                        else .error (nativeFailure .firstEntry .boundMismatch)
                      | _ => .error (nativeFailure .firstEntry .missingInternal)
                    else .error (nativeFailure .firstEntry .foreignRelation)
                else .error (nativeFailure .firstEntry .ambiguousPhysicalSlot)
              else .error (nativeFailure .firstEntry .boundMismatch)
        else .error (nativeFailure .firstEntry .wrongEntrySlot)
    else .error (nativeFailure .firstEntry .wrongEntrySlot)
  else .error (nativeFailure .firstEntry .missingInternal)

def Root.receipt {s : Source S T} {n : Native S T} {q : Request S T} (r : Root s n q) : InternalReceipt T :=
  ⟨r.value.emissionIndex,r.value.admissionIndex,r.value.emission.physical,
    r.value.emission.bound,r.value.relation,r.root⟩

def internalRoot (s : Source S T) (n : Native S T) (q : Request S T) (p : Physical T) :
    Except Failure (InternalReceipt T) := (readRoot s n q p.emissionIndex).map Root.receipt

theorem source_incidence_checked (s : Source S T) (q : Request S T) (i : Incidence s q) :
    InternalPermissionIncidenceR45.extract (SourceInternalContextR55.internalInputs s) q i.probe = some (InternalPermissionIncidenceR45.certificate q i.probe) := by
  simp [InternalPermissionIncidenceR45.extract,i.owners,i.identity]

theorem root_current_slot (s : Source S T) (n : Native S T) (q : Request S T) (r : Root s n q) :
    (current n).emissions[r.value.emissionIndex]? = some (emission r.value.emission) ∧
    (current n).admissions[r.value.emission.admission]? = some (admission r.value.admission) ∧
    CurrentEmissionOwnershipR47.currentBound (current n) (slot r.value.emission.state r.value.emission.physical) =
      some (admission r.value.admission).bound ∧
    CurrentEmissionOwnershipR47.emissionsForSlot (current n) (emission r.value.emission).physical = [emission r.value.emission] := by
  rcases r.checked with ⟨ha,he,hi,hu,_,_,_,hc,_⟩
  refine ⟨he,?_,hc,hu⟩
  change r.value.emission.admission = r.value.admissionIndex at hi
  rw [hi]
  exact ha

theorem root_source_fields (s : Source S T) (n : Native S T) (q : Request S T) (r : Root s n q) :
    CurrentEmissionOwnershipR47.RootMatches (current n) (rootQuery n q r.incidence r.root) ∧
    (current n).rootCandidates q.use r.incidence.probe.fact = [r.root] ∧
    (current n).rootCause r.root = some (q.use.occurrence,0) ∧
    (current n).rootTask r.root = some r.incidence.probe.fact ∧
    (current n).rootCompleted r.root = true := by
  have root := r.checked.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨root,root.2.1,root.2.2.2.1,root.2.2.2.2.1,root.2.2.2.2.2.1⟩

theorem complete_after_ancestry (s : Source S T) (n : Native S T) (q : Request S T)
    (r : Root s n q) (witness : List Nat)
    (ancestry : CurrentEmissionOwnershipR47.ancestryCheck (current n) r.root witness r.value.relation = true) :
    CurrentEmissionOwnershipR47.Matches (current n) (rootQuery n q r.incidence r.root)
      { physical r.value with ancestry := witness } := by
  rcases r.checked with ⟨ha,he,hi,hu,hb,hs,hh,hc,hr,hp,hroot,ho,hbo,hpol⟩
  exact ⟨ha,he,hi,hu,hb,hs,hh,hc,hr,hp,ancestry,hroot,ho,hbo,hpol⟩

/-- Entire R60 policy is now computed from inventories and the R61 schedule;
there is no independent InternalReceipt callback parameter. -/
def policy (s : Source S T) (base : Native S T) (records : List BoundedAncestryR61.Record)
    (q : Request S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule) : NativeLocalDecodeR60.Policy T :=
  BoundedAncestryR61.policy base records (internalRoot s (BoundedAncestryR61.native base records) q) schedule

def readers (s : Source S T) (base : Native S T) (records : List BoundedAncestryR61.Record)
    (q : Request S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule) : Readers S T :=
  NativeLocalDecodeR60.constructedReaders (BoundedAncestryR61.native base records) (policy s base records q schedule)

theorem same_inputs_decoder (s : Source S T) (base : Native S T) (records : List BoundedAncestryR61.Record)
    (q : Request S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (search : Search S T) :
    LocalDecode (readers s base records q schedule) (inputs (BoundedAncestryR61.native base records) search) :=
  NativeLocalDecodeR60.concrete_local_decode _ _ _

theorem callback_free_candidates_apply_consumer (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (search : Search S T)
    (q : Query) (limits : Limits) (resource : Resource) (results : List (Branch S T))
    (run : Run (readers s base records request schedule) q limits
      (.live ⟨resource,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (readers s base records request schedule) q goal)
    (terminal : goal.endpoint = q.target) :
    goal ∈ results ∧ AuthenticatedResidualConsumerR49.pathCheck
      (inputs (BoundedAncestryR61.native base records) search)
      (encodedEndpoint (readers s base records request schedule) q.root)
      (goal.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint (readers s base records request schedule) q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival (inputs (BoundedAncestryR61.native base records) search)
      (encodedEndpoint (readers s base records request schedule) q.target)
      (encodedEndpoint (readers s base records request schedule) q.root) :=
  NativeLocalDecodeR60.complete_candidates_on_constructed_inputs _ search _ q limits resource results run goal checked terminal

theorem computed_internal_success (s : Source S T) (n : Native S T) (q : Request S T)
    (p : Physical T) (receipt : InternalReceipt T)
    (success : internalRoot s n q p = .ok receipt) :
    ∃ r : Root s n q, readRoot s n q p.emissionIndex = .ok r ∧ receipt = r.receipt := by
  unfold internalRoot at success
  cases read : readRoot s n q p.emissionIndex with
  | error error => simp [read,Except.map] at success
  | ok r =>
    have same : r.receipt = receipt := by simpa [read,Except.map] using success
    exact ⟨r,rfl,same.symm⟩

/-- Apply the computed reader to the actual first-entry policy branch. The
visitor checks the returned relation before the outer physical identity check;
the result reconstructs R45 and R47 evidence on this very same native owner. -/
theorem first_entry_success_has_both_certificates (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (b : Branch S T) (p : Physical T) (result : Option Nat)
    (success : ReachedSlotSearchR58.policy (readers s base records request schedule)
      .entrySearch {b with useRoot := none,steps := []} p = .ok result) :
    ∃ r : Root s (BoundedAncestryR61.native base records) request,
      readRoot s (BoundedAncestryR61.native base records) request p.emissionIndex = .ok r ∧
      InternalPermissionIncidenceR45.extract (SourceInternalContextR55.internalInputs s)
        request r.incidence.probe = some (InternalPermissionIncidenceR45.certificate request r.incidence.probe) ∧
      (r.receipt.emissionIndex = p.emissionIndex ∧ r.receipt.admissionIndex = p.admissionIndex ∧
        r.receipt.slot = p.emission.physical ∧ r.receipt.bound = p.emission.bound) ∧
      ∃ witness, CurrentEmissionOwnershipR47.Matches
        (current (BoundedAncestryR61.native base records))
        (rootQuery (BoundedAncestryR61.native base records) request r.incidence r.root)
        {physical r.value with ancestry := witness} := by
  simp only [ReachedSlotSearchR58.policy] at success
  change (do
    let receipt ← internalRoot s (BoundedAncestryR61.native base records) request p
    let _ ← ancestryRead (readers s base records request schedule) receipt.relation receipt.useRoot
    if receipt.emissionIndex = p.emissionIndex ∧ receipt.admissionIndex = p.admissionIndex ∧
        receipt.slot = p.emission.physical ∧ receipt.bound = p.emission.bound
    then .ok (some receipt.useRoot)
    else .error (nativeFailure .firstEntry .boundMismatch)) = .ok result at success
  cases read : readRoot s (BoundedAncestryR61.native base records) request p.emissionIndex with
  | error error => simp [internalRoot,read,Except.map,Bind.bind,Except.bind] at success
  | ok r =>
    simp only [internalRoot,read,Except.map,Bind.bind,Except.bind] at success
    cases ancestry : ancestryRead (readers s base records request schedule) r.receipt.relation r.receipt.useRoot with
    | error error => simp [ancestry] at success
    | ok answer =>
      cases answer
      simp only [ancestry] at success
      split at success
      next same =>
        have sound := BoundedAncestryR61.constructed_ancestry_read_is_sound base records
          (internalRoot s (BoundedAncestryR61.native base records) request) schedule
          r.value.relation r.root ancestry
        obtain ⟨witness,checked⟩ := sound.2
        exact ⟨r,rfl,source_incidence_checked s request r.incidence,same,
          witness,complete_after_ancestry s _ request r witness checked⟩
      next different => cases success

theorem root_native_projection (s : Source S T) (n : Native S T) (q : Request S T)
    (r : Root s n q) :
    (originRead n r.root).map (fun o => (Key.source o.occurrence,o.slot)) =
      some (q.use.occurrence,0) ∧
    (rootDrain n r.root).map (fun d => (Key.source d.cause,d.slot)) =
      some (q.use.occurrence,0) ∧
    rootTask n r.root = some r.incidence.probe.fact ∧ completed n r.root = true ∧
    sourceFact n (q.use.occurrence,0) = some r.incidence.probe.fact := by
  have h := (root_source_fields s n q r).1
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem source_failure_precedes_ancestry (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (b : Branch S T)
    (p : Physical T) (error : Failure)
    (failed : readRoot s (BoundedAncestryR61.native base records) request p.emissionIndex = .error error) :
    ReachedSlotSearchR58.policy (readers s base records request schedule)
      .entrySearch {b with useRoot := none,steps := []} p = .error error := by
  change (do
    let receipt ← internalRoot s (BoundedAncestryR61.native base records) request p
    let _ ← ancestryRead (readers s base records request schedule) receipt.relation receipt.useRoot
    if receipt.emissionIndex = p.emissionIndex ∧ receipt.admissionIndex = p.admissionIndex ∧
        receipt.slot = p.emission.physical ∧ receipt.bound = p.emission.bound
    then .ok (some receipt.useRoot)
    else .error (nativeFailure .firstEntry .boundMismatch)) = .error error
  simp [internalRoot,failed,Except.map,Bind.bind,Except.bind]

theorem ancestry_failure_precedes_outer_identity (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (b : Branch S T) (p : Physical T)
    (r : Root s (BoundedAncestryR61.native base records) request) (error : Failure)
    (read : readRoot s (BoundedAncestryR61.native base records) request p.emissionIndex = .ok r)
    (failed : ancestryRead (readers s base records request schedule) r.receipt.relation r.receipt.useRoot = .error error) :
    ReachedSlotSearchR58.policy (readers s base records request schedule)
      .entrySearch {b with useRoot := none,steps := []} p = .error error := by
  change (do
    let receipt ← internalRoot s (BoundedAncestryR61.native base records) request p
    let _ ← ancestryRead (readers s base records request schedule) receipt.relation receipt.useRoot
    if receipt.emissionIndex = p.emissionIndex ∧ receipt.admissionIndex = p.admissionIndex ∧
        receipt.slot = p.emission.physical ∧ receipt.bound = p.emission.bound
    then .ok (some receipt.useRoot)
    else .error (nativeFailure .firstEntry .boundMismatch)) = .error error
  simp [internalRoot,read,Except.map,Bind.bind,Except.bind,failed]

theorem later_entry_has_directed_ancestry (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (b : Branch S T) (p : Physical T)
    (root : Nat) (head : PathStep S T) (tail : List (PathStep S T))
    (success : ReachedSlotSearchR58.policy (readers s base records request schedule)
      .entrySearch {b with useRoot := some root,steps := head::tail} p = .ok (some root)) :
    CurrentEmissionOwnershipR47.RelationPath (current (BoundedAncestryR61.native base records)) root p.relation :=
  BoundedAncestryR61.later_entry_policy_has_directed_ancestry base records
    (internalRoot s (BoundedAncestryR61.native base records) request) schedule b p root head tail success

theorem catch_keeps_existing_policy (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (b : Branch S T) (p : Physical T) :
    ReachedSlotSearchR58.policy (readers s base records request schedule) .catchSearch b p = .ok none :=
  BoundedAncestryR61.catch_policy_skips_the_visitor base records
    (internalRoot s (BoundedAncestryR61.native base records) request) schedule b p

theorem callback_free_candidate_iff (s : Source S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (q : Query) (limits : Limits)
    (resource : Resource) (results : List (Branch S T))
    (run : Run (readers s base records request schedule) q limits
      (.live ⟨resource,[initial q],[],.pop⟩) (.success results)) (goal : Branch S T) :
    goal ∈ results ↔ Checked (readers s base records request schedule) q goal ∧ goal.endpoint = q.target :=
  by
    constructor
    · exact ReachedSlotSearchR58.successful_results_checked _ q limits resource results run goal
    · rintro ⟨checked,terminal⟩
      exact ReachedSlotCompletenessR59.initial_success_contains_every_checked_target
        _ q limits resource results run goal checked terminal

/- Finite computations over the existing primitive R57 fixture; these do not
assert that an actual Rust execution emitted those inventories. -/
def fixtureRequest : Request Nat Nat := SourceInternalContextR55.query ProviderNativeContextR57.fixtureQuery
def fixtureRecords : List BoundedAncestryR61.Record := [.derived 0 2]
def fixtureSchedule (_ _ : Nat) : BoundedAncestryR61.Schedule := ⟨10,List.replicate 10 true⟩
def fixturePhysical : Physical Nat := ProviderNativeContextR57.fixturePhysical 4 0 0 []
def fixtureBranch : Branch Nat Nat := initial ⟨.row 4,.annotationMember 0 0,.entrySearch⟩

theorem computed_fixture_receipt :
    internalRoot fixtureInternal fixtureNative fixtureRequest fixturePhysical =
      .ok ⟨0,0,fixtureSlot 4,fixtureBound 4,0,2⟩ := rfl

theorem computed_fixture_first_entry :
    ReachedSlotSearchR58.policy (readers fixtureInternal fixtureNative fixtureRecords fixtureRequest fixtureSchedule)
      .entrySearch fixtureBranch fixturePhysical = .ok (some 2) := rfl

theorem computed_fixture_missing_duplicate_and_foreign :
    internalRoot {fixtureInternal with permissions := []} fixtureNative fixtureRequest fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot {fixtureInternal with permissions := fixtureInternal.permissions ++ fixtureInternal.permissions}
      fixtureNative fixtureRequest fixturePhysical = .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot {fixtureInternal with constructions := fixtureInternal.constructions ++ fixtureInternal.constructions}
      fixtureNative fixtureRequest fixturePhysical = .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot fixtureInternal fixtureNative {fixtureRequest with targetOwner := .source 9} fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot fixtureInternal fixtureNative {fixtureRequest with use := ⟨98,.source 100⟩} fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot fixtureInternal {fixtureNative with origins := []} fixtureRequest fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot fixtureInternal {fixtureNative with origins := fixtureNative.origins ++ fixtureNative.origins}
      fixtureRequest fixturePhysical = .error (nativeFailure .firstEntry .missingInternal) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem computed_fixture_stale_slot_and_drain :
    internalRoot fixtureInternal {fixtureNative with effectRows := []} fixtureRequest fixturePhysical =
      .error (nativeFailure .firstEntry .boundMismatch) ∧
    internalRoot fixtureInternal {fixtureNative with emissions :=
      [{(ProviderNativeContextR57.fixtureEmission 4 0) with physical := fixtureSlot 5}]}
      fixtureRequest fixturePhysical = .error (nativeFailure .firstEntry .wrongEntrySlot) ∧
    internalRoot fixtureInternal {fixtureNative with origins := fixtureNative.origins.map (fun o => {o with drain := o.drain.map (fun d => {d with cause := 101})})}
      fixtureRequest fixturePhysical = .error (nativeFailure .firstEntry .boundMismatch) ∧
    internalRoot fixtureInternal {fixtureNative with origins := fixtureNative.origins.map (fun o => {o with drain := o.drain.map (fun d => {d with completed := false})})}
      fixtureRequest fixturePhysical = .error (nativeFailure .firstEntry .boundMismatch) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem computed_fixture_ancestry_before_outer_mismatch :
    ReachedSlotSearchR58.policy (readers fixtureInternal fixtureNative [] fixtureRequest fixtureSchedule)
      .entrySearch fixtureBranch {fixturePhysical with admissionIndex := 99} =
      .error (nativeFailure .laterAncestry .missingUseAncestry) := rfl

end YulangClosure.InternalRootPolicyR62
