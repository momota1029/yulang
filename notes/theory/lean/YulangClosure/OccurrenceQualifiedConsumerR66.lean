import YulangClosure.OccurrenceQualifiedFactReadersR65
import YulangClosure.InternalRootPolicyR62

/-!
R66 versioned computed first-entry policy and R49 consumer. Semantic route and
construction facts, root tasks and root candidates use R65 occurrence-qualified
readers throughout. R55/R57 source metadata and physical projections are retained;
no old global-FactId semantic reader is used by these adapters. This finite model
does not assert source extraction, native execution or original A/B closure.
-/
namespace YulangClosure.OccurrenceQualifiedConsumerR66
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
def sourceProbe (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) : Option (InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact) := do
  let e := OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence
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

structure Incidence (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) where
  probe : InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact
  read : sourceProbe s inventory q = some probe
  owners : InternalPermissionIncidenceR45.OwnerReads (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q probe
  identity : InternalPermissionIncidenceR45.Identity (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q probe
  parameterRecipe : s.parameterRecipes[probe.formal.recipe]? = some probe.formal.parameter

def incidence (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) : Except Failure (Incidence s inventory q) :=
  match read : sourceProbe s inventory q with
  | none => .error (nativeFailure .firstEntry .missingInternal)
  | some probe => if checked : InternalPermissionIncidenceR45.OwnerReads (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q probe ∧
      InternalPermissionIncidenceR45.Identity (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q probe ∧
      s.parameterRecipes[probe.formal.recipe]? = some probe.formal.parameter then
        .ok ⟨probe,read,checked.1,checked.2.1,checked.2.2⟩
    else .error (nativeFailure .firstEntry .missingInternal)

def rootQuery (_n : Native S T) (q : Request S T) (i : Incidence s inventory q) (root : Nat) :
    CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact := ⟨q.use,i.probe.fact,i.probe.permission.entry,root⟩

/-- Exactly R47 Matches with the ancestry conjunct removed. Ancestry is run
only after this certificate exists; it cannot be used to choose a source root. -/
def BeforeAncestry (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact)
    (p : CurrentEmissionOwnershipR47.Probe (Key S T)) : Prop :=
  (OccurrenceQualifiedFactReadersR65.current n inventory).admissions[p.admissionIndex]? = some p.admission ∧
  (OccurrenceQualifiedFactReadersR65.current n inventory).emissions[p.emissionIndex]? = some p.emission ∧
  p.emission.admission = p.admissionIndex ∧
  CurrentEmissionOwnershipR47.emissionsForSlot (OccurrenceQualifiedFactReadersR65.current n inventory) p.emission.physical = [p.emission] ∧
  p.emission.bound = p.admission.bound ∧ p.emission.readback.slot = p.emission.physical ∧
  p.emission.readback.bound = p.admission.bound ∧
  CurrentEmissionOwnershipR47.currentBound (OccurrenceQualifiedFactReadersR65.current n inventory) p.emission.physical = some p.admission.bound ∧
  p.admission.relation = some p.relation ∧
  (OccurrenceQualifiedFactReadersR65.current n inventory).relationPair p.relation = some (CurrentEmissionOwnershipR47.boundPair p.admission.bound) ∧
  CurrentEmissionOwnershipR47.RootMatches (OccurrenceQualifiedFactReadersR65.current n inventory) q ∧
  p.emission.physical.owner = .effect q.rawEntry ∧
  p.admission.bound.owner = .effect q.rawEntry ∧ p.admission.bound.polarity = .positive

instance (n : Native S T) (q : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact) (p : CurrentEmissionOwnershipR47.Probe (Key S T)) :
    Decidable (BeforeAncestry inventory n q p) := by unfold BeforeAncestry; infer_instance

structure Root (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T) where
  incidence : Incidence s inventory q
  sameArtifact : s.artifact = n.artifact
  entry : incidence.probe.permission.entry = .effectRow n.state n.entryRow
  value : Physical T
  root : Nat
  checked : BeforeAncestry inventory n (rootQuery n q incidence root) (physical value)

/-- Source incidence first; then the selected native emission/current slot,
indexed admission/relation and unique source drain. No ancestry is evaluated. -/
def readRoot (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T) (index : Nat) :
    Except Failure (Root s inventory n q) := do
  let i ← incidence s inventory q
  if same : s.artifact = n.artifact then
    if entry : i.probe.permission.entry = .effectRow n.state n.entryRow then
      match n.emissions[index]? with
      | none => .error (nativeFailure .firstEntry .missingEmission)
      | some e =>
        if e.physical.owner = .effect n.entryRow ∧
            (e.physical.lane = .effectLowerRow ∨ e.physical.lane = .effectLowerAtom) then
          match CurrentEmissionOwnershipR47.currentBound (OccurrenceQualifiedFactReadersR65.current n inventory) (emission e).physical with
          | none => .error (nativeFailure .firstEntry .boundMismatch)
          | some fresh => match n.admissions[e.admission]? with
            | none => .error (nativeFailure .firstEntry .missingAdmission)
            | some a =>
              if (emission (S := S) e).bound = (admission a).bound ∧
                  (emission (S := S) e).bound = (emission e).readback.bound ∧
                  (emission (S := S) e).physical = (emission e).readback.slot ∧
                  (emission (S := S) e).bound = fresh then
                if CurrentEmissionOwnershipR47.emissionsForSlot (OccurrenceQualifiedFactReadersR65.current n inventory) (emission e).physical = [emission e] then
                  match a.relation with
                  | none => .error (nativeFailure .firstEntry .missingRelation)
                  | some relation =>
                    if (OccurrenceQualifiedFactReadersR65.current n inventory).relationPair relation = some (CurrentEmissionOwnershipR47.boundPair (admission a).bound) then
                      match (OccurrenceQualifiedFactReadersR65.current n inventory).rootCandidates q.use i.probe.fact with
                      | [root] =>
                        let value : Physical T := ⟨e.admission,index,a,e,relation,[]⟩
                        if checked : BeforeAncestry inventory n (rootQuery n q i root) (physical value) then
                          .ok ⟨i,same,entry,value,root,checked⟩
                        else .error (nativeFailure .firstEntry .boundMismatch)
                      | _ => .error (nativeFailure .firstEntry .missingInternal)
                    else .error (nativeFailure .firstEntry .foreignRelation)
                else .error (nativeFailure .firstEntry .ambiguousPhysicalSlot)
              else .error (nativeFailure .firstEntry .boundMismatch)
        else .error (nativeFailure .firstEntry .wrongEntrySlot)
    else .error (nativeFailure .firstEntry .wrongEntrySlot)
  else .error (nativeFailure .firstEntry .missingInternal)

def Root.receipt {s : Source S T} {n : Native S T} {q : Request S T} (r : Root s inventory n q) : InternalReceipt T :=
  ⟨r.value.emissionIndex,r.value.admissionIndex,r.value.emission.physical,
    r.value.emission.bound,r.value.relation,r.root⟩

def internalRoot (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T) (p : Physical T) :
    Except Failure (InternalReceipt T) := (readRoot s inventory n q p.emissionIndex).map Root.receipt

theorem source_incidence_checked (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) (i : Incidence s inventory q) :
    InternalPermissionIncidenceR45.extract (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q i.probe = some (InternalPermissionIncidenceR45.certificate q i.probe) := by
  simp [InternalPermissionIncidenceR45.extract,i.owners,i.identity]

theorem root_current_slot (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T) (r : Root s inventory n q) :
    (OccurrenceQualifiedFactReadersR65.current n inventory).emissions[r.value.emissionIndex]? = some (emission r.value.emission) ∧
    (OccurrenceQualifiedFactReadersR65.current n inventory).admissions[r.value.emission.admission]? = some (admission r.value.admission) ∧
    CurrentEmissionOwnershipR47.currentBound (OccurrenceQualifiedFactReadersR65.current n inventory) (slot r.value.emission.state r.value.emission.physical) =
      some (admission r.value.admission).bound ∧
    CurrentEmissionOwnershipR47.emissionsForSlot (OccurrenceQualifiedFactReadersR65.current n inventory) (emission r.value.emission).physical = [emission r.value.emission] := by
  rcases r.checked with ⟨ha,he,hi,hu,_,_,_,hc,_⟩
  refine ⟨he,?_,hc,hu⟩
  change r.value.emission.admission = r.value.admissionIndex at hi
  rw [hi]
  exact ha

theorem root_source_fields (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T) (r : Root s inventory n q) :
    CurrentEmissionOwnershipR47.RootMatches (OccurrenceQualifiedFactReadersR65.current n inventory) (rootQuery n q r.incidence r.root) ∧
    (OccurrenceQualifiedFactReadersR65.current n inventory).rootCandidates q.use r.incidence.probe.fact = [r.root] ∧
    (OccurrenceQualifiedFactReadersR65.current n inventory).rootCause r.root = some (q.use.occurrence,0) ∧
    (OccurrenceQualifiedFactReadersR65.current n inventory).rootTask r.root = some r.incidence.probe.fact ∧
    (OccurrenceQualifiedFactReadersR65.current n inventory).rootCompleted r.root = true := by
  have root := r.checked.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨root,root.2.1,root.2.2.2.1,root.2.2.2.2.1,root.2.2.2.2.2.1⟩

theorem complete_after_ancestry (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T)
    (r : Root s inventory n q) (witness : List Nat)
    (ancestry : CurrentEmissionOwnershipR47.ancestryCheck (OccurrenceQualifiedFactReadersR65.current n inventory) r.root witness r.value.relation = true) :
    CurrentEmissionOwnershipR47.Matches (OccurrenceQualifiedFactReadersR65.current n inventory) (rootQuery n q r.incidence r.root)
      { physical r.value with ancestry := witness } := by
  rcases r.checked with ⟨ha,he,hi,hu,hb,hs,hh,hc,hr,hp,hroot,ho,hbo,hpol⟩
  exact ⟨ha,he,hi,hu,hb,hs,hh,hc,hr,hp,ancestry,hroot,ho,hbo,hpol⟩

/-- Entire R60 policy is now computed from inventories and the R61 schedule;
there is no independent InternalReceipt callback parameter. -/
def policy (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (base : Native S T) (records : List BoundedAncestryR61.Record)
    (q : Request S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule) : NativeLocalDecodeR60.Policy T :=
  BoundedAncestryR61.policy base records (internalRoot s inventory (BoundedAncestryR61.native base records) q) schedule

def readers (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (base : Native S T) (records : List BoundedAncestryR61.Record)
    (q : Request S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule) : Readers S T :=
  NativeLocalDecodeR60.constructedReaders (BoundedAncestryR61.native base records) (policy s inventory base records q schedule)

theorem computed_internal_success (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T)
    (p : Physical T) (receipt : InternalReceipt T)
    (success : internalRoot s inventory n q p = .ok receipt) :
    ∃ r : Root s inventory n q, readRoot s inventory n q p.emissionIndex = .ok r ∧ receipt = r.receipt := by
  unfold internalRoot at success
  cases read : readRoot s inventory n q p.emissionIndex with
  | error error => simp [read,Except.map] at success
  | ok r =>
    have same : r.receipt = receipt := by simpa [read,Except.map] using success
    exact ⟨r,rfl,same.symm⟩

/-- Apply the computed reader to the actual first-entry policy branch. The
visitor checks the returned relation before the outer physical identity check;
the result reconstructs R45 and R47 evidence on this very same native owner. -/
theorem ancestry_reader_agreement (n : Native S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (root : Nat) (witness : List Nat) (target : Nat) :
    CurrentEmissionOwnershipR47.ancestryCheck (OccurrenceQualifiedFactReadersR65.current n inventory) root witness target =
      CurrentEmissionOwnershipR47.ancestryCheck (ProviderNativeContextR57.current n) root witness target := by
  induction witness generalizing root with
  | nil => rfl
  | cons child rest ih =>
    simp only [CurrentEmissionOwnershipR47.ancestryCheck,ih]
    rfl

theorem first_entry_success_has_both_certificates (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (b : Branch S T) (p : Physical T) (result : Option Nat)
    (success : ReachedSlotSearchR58.policy (readers s inventory base records request schedule)
      .entrySearch {b with useRoot := none,steps := []} p = .ok result) :
    ∃ r : Root s inventory (BoundedAncestryR61.native base records) request,
      readRoot s inventory (BoundedAncestryR61.native base records) request p.emissionIndex = .ok r ∧
      InternalPermissionIncidenceR45.extract (OccurrenceQualifiedFactReadersR65.internalInputs s inventory request.use.occurrence)
        request r.incidence.probe = some (InternalPermissionIncidenceR45.certificate request r.incidence.probe) ∧
      (r.receipt.emissionIndex = p.emissionIndex ∧ r.receipt.admissionIndex = p.admissionIndex ∧
        r.receipt.slot = p.emission.physical ∧ r.receipt.bound = p.emission.bound) ∧
      ∃ witness, CurrentEmissionOwnershipR47.Matches
        (OccurrenceQualifiedFactReadersR65.current (BoundedAncestryR61.native base records) inventory)
        (rootQuery (BoundedAncestryR61.native base records) request r.incidence r.root)
        {physical r.value with ancestry := witness} := by
  simp only [ReachedSlotSearchR58.policy] at success
  change (do
    let receipt ← internalRoot s inventory (BoundedAncestryR61.native base records) request p
    let _ ← ancestryRead (readers s inventory base records request schedule) receipt.relation receipt.useRoot
    if receipt.emissionIndex = p.emissionIndex ∧ receipt.admissionIndex = p.admissionIndex ∧
        receipt.slot = p.emission.physical ∧ receipt.bound = p.emission.bound
    then .ok (some receipt.useRoot)
    else .error (nativeFailure .firstEntry .boundMismatch)) = .ok result at success
  cases read : readRoot s inventory (BoundedAncestryR61.native base records) request p.emissionIndex with
  | error error => simp [internalRoot,read,Except.map,Bind.bind,Except.bind] at success
  | ok r =>
    simp only [internalRoot,read,Except.map,Bind.bind,Except.bind] at success
    cases ancestry : ancestryRead (readers s inventory base records request schedule) r.receipt.relation r.receipt.useRoot with
    | error error => simp [ancestry] at success
    | ok answer =>
      cases answer
      simp only [ancestry] at success
      split at success
      next same =>
        have sound := BoundedAncestryR61.constructed_ancestry_read_is_sound base records
          (internalRoot s inventory (BoundedAncestryR61.native base records) request) schedule
          r.value.relation r.root ancestry
        obtain ⟨witness,checked⟩ := sound.2
        exact ⟨r,rfl,source_incidence_checked s inventory request r.incidence,same,
          witness,complete_after_ancestry s inventory _ request r witness (by rw [ancestry_reader_agreement]; exact checked)⟩
      next different => cases success



/-- The Catch/physical/source-operation projections are retained; the current
semantic source/root fields are replaced by the very same R65 inventory. -/
def consumerInputs (n : Native S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (search : Search S T) : AuthenticatedResidualConsumerR49.Inputs Nat (Key S T) Fact :=
  { ProviderNativeContextR57.inputs n search with
    arrival := { ProviderNativeContextR57.arrival n with
      current := OccurrenceQualifiedFactReadersR65.current n inventory } }

/-- All sensitive Context fields are constructed from one computed root.
The remaining source arms/provider paths are independently retained evidence. -/
def context (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (n : Native S T) (q : Request S T) (r : Root s inventory n q)
    (witness : List Nat) (search : Search S T)
    (catches : List (SourceInternalContextR55.Catch (Key S T)))
    (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (provider : Provider S T) :
    AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact :=
  ⟨OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence,
    q,r.incidence.probe,InternalPermissionIncidenceR45.certificate q r.incidence.probe,
    consumerInputs n inventory search,SourceInternalContextR55.catchInputs catches operations,
    rootQuery n q r.incidence r.root,{physical r.value with ancestry := witness},
    providerQuery n provider,
    ⟨provider.entryTail.map step,provider.catchPath.map step,terminal n provider,
      SourceInternalContextR55.selection selection⟩⟩

/-- These are precisely the still-independent R49 consumer premises after
Internal/current ownership and the same use/fact/raw-entry joins are derived.
They are not a concrete source-instance or native-execution theorem. -/
structure ConsumerEvidence (c : AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact) : Prop where
  family : c.query.family ∈ c.internal.permission.concrete
  provider : c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family = [c.probe.terminal.atom]
  entryUnique : c.inputs.pathCandidates (.effectRow c.entryQuery.rawEntry) (.effectAtom c.probe.terminal.atom) =
    [.physical c.entryProbe :: c.probe.entryTail]
  catchUnique : c.inputs.pathCandidates c.query.catchInput (.effectAtom c.probe.terminal.atom) = [c.probe.catchPath]
  entryPath : AuthenticatedResidualConsumerR49.pathCheck c.inputs (.effectRow c.entryQuery.rawEntry)
    (.physical c.entryProbe :: c.probe.entryTail) (.effectAtom c.probe.terminal.atom) = true
  catchReads : ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query
  catchPath : AuthenticatedResidualConsumerR49.pathCheck c.inputs c.query.catchInput c.probe.catchPath
    (.effectAtom c.probe.terminal.atom) = true
  terminalReads : ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal
  closed : c.probe.terminal.view.tail = none
  arm : AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection

theorem context_authenticates (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (n : Native S T) (q : Request S T) (r : Root s inventory n q) (witness : List Nat)
    (search : Search S T) (catches : List (SourceInternalContextR55.Catch (Key S T)))
    (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (provider : Provider S T)
    (ancestry : CurrentEmissionOwnershipR47.ancestryCheck (OccurrenceQualifiedFactReadersR65.current n inventory)
      r.root witness r.value.relation = true)
    (evidence : ConsumerEvidence (context s inventory n q r witness search catches operations selection provider)) :
    AuthenticatedResidualConsumerR49.authenticate
      (context s inventory n q r witness search catches operations selection provider) = true := by
  apply decide_eq_true
  exact ⟨source_incidence_checked s inventory q r.incidence,
    complete_after_ancestry s inventory n q r witness ancestry,rfl,rfl,rfl,
    evidence.family,evidence.provider,evidence.entryUnique,evidence.catchUnique,evidence.entryPath,
    evidence.catchReads,evidence.catchPath,evidence.terminalReads,evidence.closed,evidence.arm⟩

/-- Apply first-entry success to this exact R49 Context. All remaining
consumer evidence is explicit under the returned root and ancestry witness. -/
theorem first_entry_applies_consumer (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (base : Native S T) (records : List BoundedAncestryR61.Record) (q : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (b : Branch S T) (p : Physical T)
    (result : Option Nat) (search : Search S T)
    (catches : List (SourceInternalContextR55.Catch (Key S T)))
    (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (provider : Provider S T)
    (success : ReachedSlotSearchR58.policy (readers s inventory base records q schedule)
      .entrySearch {b with useRoot := none,steps := []} p = .ok result) :
    ∃ (r : Root s inventory (BoundedAncestryR61.native base records) q) (witness : List Nat),
      readRoot s inventory (BoundedAncestryR61.native base records) q p.emissionIndex = .ok r ∧
      (ConsumerEvidence (context s inventory (BoundedAncestryR61.native base records) q r witness
        search catches operations selection provider) →
       AuthenticatedResidualConsumerR49.authenticate
         (context s inventory (BoundedAncestryR61.native base records) q r witness search catches operations selection provider) = true ∧
       AuthenticatedResidualConsumerR49.decideEndpoint
         (context s inventory (BoundedAncestryR61.native base records) q r witness search catches operations selection provider)
         (AuthenticatedResidualConsumerR49.target
           (context s inventory (BoundedAncestryR61.native base records) q r witness search catches operations selection provider)) = some .suppress) := by
  obtain ⟨r,read,_,_,witness,matched⟩ :=
    first_entry_success_has_both_certificates s inventory base records q schedule b p result success
  refine ⟨r,witness,read,?_⟩
  intro evidence
  have ancestry := matched.2.2.2.2.2.2.2.2.2.2.1
  have auth := context_authenticates s inventory _ q r witness search catches operations selection provider ancestry evidence
  exact ⟨auth,(AuthenticatedResidualConsumerR49.suppression_iff _ _).mpr ⟨rfl,auth⟩⟩

/-- Successful outer Run remains an independent premise of candidate coverage;
this statement supplies no Run from local policy or consumer acceptance. -/
theorem successful_outer_run_contains_checked (s : Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (q : Query)
    (limits : Limits) (resource : Resource) (results : List (Branch S T))
    (run : Run (readers s inventory base records request schedule) q limits
      (.live ⟨resource,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (readers s inventory base records request schedule) q goal)
    (terminal : goal.endpoint = q.target) : goal ∈ results :=
  ReachedSlotCompletenessR59.initial_success_contains_every_checked_target _ q limits resource results run goal checked terminal


/-- Exact projections keep the certificate, full permission and raw entry
shared with the selected qualified route and R47 root, without a mirror Context. -/
theorem context_same_objects (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (n : Native S T) (q : Request S T) (r : Root s inventory n q) (witness : List Nat)
    (search : Search S T) (catches : List (SourceInternalContextR55.Catch (Key S T)))
    (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (provider : Provider S T) :
    let c := context s inventory n q r witness search catches operations selection provider
    c.internalInputs = OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence ∧
    c.inputs.arrival.current = OccurrenceQualifiedFactReadersR65.current n inventory ∧
    c.internal.use = q.use ∧ c.internal.fact = r.incidence.probe.fact ∧
    c.internal.permission = r.incidence.probe.permission ∧
    c.entryQuery.use = c.internal.use ∧ c.entryQuery.internalFact = c.internal.fact ∧
    c.entryQuery.rawEntry = c.internal.permission.entry ∧ c.entryQuery.rootRelation = r.root := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem selected_root_has_qualified_source_reads (s : Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : Request S T) (r : Root s inventory n q) (occurrence lambda : S)
    (useCoordinate : q.use.occurrence = .source occurrence) (lambdaCoordinate : q.lambda = .source lambda) :
    ∃ route construction,
      OccurrenceQualifiedFactReadersR65.readAt inventory occurrence 0 = some route ∧
      route.fact.identity = r.incidence.probe.fact ∧
      route.fact.lower = r.incidence.probe.registeredRoot ∧
      route.fact.upper = r.incidence.probe.plan.useValue ∧
      OccurrenceQualifiedFactReadersR65.readAt inventory lambda 2 = some construction ∧
      construction.fact.lower = r.incidence.probe.construction.function ∧
      construction.fact.upper = r.incidence.probe.registeredRoot :=
  OccurrenceQualifiedFactReadersR65.qualified_internal_source_facts s inventory q r.incidence.probe
    (InternalPermissionIncidenceR45.certificate q r.incidence.probe)
    (source_incidence_checked s inventory q r.incidence) occurrence lambda useCoordinate lambdaCoordinate

/-! Finite mathematical inventories only. The two occurrence keys share one
semantic FactId; no successful native execution or outer Run is asserted. -/
def fixtureRecords : List BoundedAncestryR61.Record := [.derived 0 2]
def fixtureNative := BoundedAncestryR61.native ProviderNativeContextR57.fixtureNative fixtureRecords
def fixtureSchedule (_ _ : Nat) : BoundedAncestryR61.Schedule := ⟨10,List.replicate 10 true⟩
def fixturePhysical : Physical Nat := ProviderNativeContextR57.fixturePhysical 4 0 0 []
def fixtureBranch : Branch Nat Nat := initial ⟨.row 4,.annotationMember 0 0,.entrySearch⟩
def fixtureIncidence : Incidence OccurrenceQualifiedFactReadersR65.fixtureSource
    OccurrenceQualifiedFactReadersR65.fixtureInventory OccurrenceQualifiedFactReadersR65.fixtureInternalQuery :=
  ⟨OccurrenceQualifiedFactReadersR65.fixtureInternalProbe,rfl,by decide,by decide,rfl⟩
def fixtureRoot : Root OccurrenceQualifiedFactReadersR65.fixtureSource
    OccurrenceQualifiedFactReadersR65.fixtureInventory fixtureNative
    OccurrenceQualifiedFactReadersR65.fixtureInternalQuery :=
  ⟨fixtureIncidence,rfl,rfl,fixturePhysical,2,by decide⟩
def fixtureContext := context OccurrenceQualifiedFactReadersR65.fixtureSource
  OccurrenceQualifiedFactReadersR65.fixtureInventory fixtureNative
  OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixtureRoot [0]
  ProviderNativeContextR57.fixtureSearch [ProviderNativeContextR57.fixtureCatch]
  [ProviderNativeContextR57.fixtureOperation] ProviderNativeContextR57.fixtureSelection
  ProviderNativeContextR57.fixtureProvider

theorem finite_shared_fact_policy_and_consumer :
    OccurrenceQualifiedFactReadersR65.fixtureFirst.fact = OccurrenceQualifiedFactReadersR65.fixtureSecond.fact ∧
    OccurrenceQualifiedFactReadersR65.fixtureFirst.occurrence ≠ OccurrenceQualifiedFactReadersR65.fixtureSecond.occurrence ∧
    OccurrenceQualifiedFactReadersR65.readAt OccurrenceQualifiedFactReadersR65.fixtureInventory 100 0 =
      some ⟨OccurrenceQualifiedFactReadersR65.fixtureFirst,OccurrenceQualifiedFactReadersR65.fixtureRoute⟩ ∧
    OccurrenceQualifiedFactReadersR65.readAt OccurrenceQualifiedFactReadersR65.fixtureInventory 101 0 =
      some ⟨OccurrenceQualifiedFactReadersR65.fixtureSecond,OccurrenceQualifiedFactReadersR65.fixtureRoute⟩ ∧
    readRoot OccurrenceQualifiedFactReadersR65.fixtureSource OccurrenceQualifiedFactReadersR65.fixtureInventory
      fixtureNative OccurrenceQualifiedFactReadersR65.fixtureInternalQuery 0 = .ok fixtureRoot ∧
    ReachedSlotSearchR58.policy
      (readers OccurrenceQualifiedFactReadersR65.fixtureSource OccurrenceQualifiedFactReadersR65.fixtureInventory
        ProviderNativeContextR57.fixtureNative fixtureRecords OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixtureSchedule)
      .entrySearch fixtureBranch fixturePhysical = .ok (some 2) ∧
    AuthenticatedResidualConsumerR49.authenticate fixtureContext = true ∧
    fixtureContext.internal.fact = .semantic 2 0 ∧
    fixtureContext.entryQuery.internalFact = fixtureContext.internal.fact ∧
    fixtureContext.internal.permission = fixtureRoot.incidence.probe.permission ∧
    fixtureContext.entryQuery.rawEntry = fixtureContext.internal.permission.entry ∧
    AuthenticatedResidualConsumerR49.publish fixtureContext
      [.effectAtom (.effectAtom 1 (.annotationMember 0 0)),.effectAtom (.effectAtom 1 (.contribution 8))]
      (.effectRow (.effectRow 1 7)) = some [(.effectAtom (.effectAtom 1 (.contribution 8)),.effectRow (.effectRow 1 7))] := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,by decide⟩


theorem current_bound_agreement (n : Native S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (slot : CurrentEmissionOwnershipR47.Slot (Key S T)) :
    CurrentEmissionOwnershipR47.currentBound (OccurrenceQualifiedFactReadersR65.current n inventory) slot =
      CurrentEmissionOwnershipR47.currentBound (ProviderNativeContextR57.current n) slot := by
  rcases slot with ⟨owner,lane,index⟩
  cases owner <;> cases lane <;> rfl

theorem consumer_edge_reads_agreement (n : Native S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (search : Search S T)
    (root : CurrentEmissionOwnershipR47.Endpoint (Key S T))
    (p : CurrentEmissionOwnershipR47.Probe (Key S T)) :
    ProviderEntryArrivalR48.EdgeReads (consumerInputs n inventory search).arrival root p ↔
      ProviderEntryArrivalR48.EdgeReads (ProviderNativeContextR57.arrival n) root p := by
  simp only [consumerInputs,ProviderEntryArrivalR48.EdgeReads]
  rw [current_bound_agreement]
  rfl

/-- Reuse R60's actual physical decoder, proving the qualified update commutes
with its reads. No LocalDecode law is supplied as an assumption. -/
theorem qualified_local_decode (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (base : Native S T) (records : List BoundedAncestryR61.Record) (q : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (search : Search S T) :
    LocalDecode (readers s inventory base records q schedule)
      (consumerInputs (BoundedAncestryR61.native base records) inventory search) := by
  have original := NativeLocalDecodeR60.concrete_local_decode (BoundedAncestryR61.native base records)
    search (policy s inventory base records q schedule)
  constructor
  · intro row cell p read
    obtain ⟨edge,next⟩ := original.physical row cell p read
    exact ⟨(consumer_edge_reads_agreement _ inventory search _ _).mpr edge,next⟩
  · intro index v family ordinal read owned closed member
    exact original.support index v family ordinal read owned closed member

/-- R62/R61 successful outer search application, with concrete qualified
LocalDecode. Run, Checked and terminal equality remain separate premises. -/
theorem qualified_candidates_apply_consumer (s : Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (base : Native S T)
    (records : List BoundedAncestryR61.Record) (request : Request S T)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (search : Search S T) (q : Query)
    (limits : Limits) (resource : Resource) (results : List (Branch S T))
    (run : Run (readers s inventory base records request schedule) q limits
      (.live ⟨resource,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (readers s inventory base records request schedule) q goal)
    (terminal : goal.endpoint = q.target) :
    goal ∈ results ∧
    AuthenticatedResidualConsumerR49.pathCheck
      (consumerInputs (BoundedAncestryR61.native base records) inventory search)
      (encodedEndpoint (readers s inventory base records request schedule) q.root)
      (goal.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint (readers s inventory base records request schedule) q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival
      (consumerInputs (BoundedAncestryR61.native base records) inventory search)
      (encodedEndpoint (readers s inventory base records request schedule) q.target)
      (encodedEndpoint (readers s inventory base records request schedule) q.root) :=
  ReachedSlotCompletenessR59.complete_candidates_apply_existing_consumer
    _ q limits resource results run goal checked terminal _
    (qualified_local_decode s inventory base records request schedule search)

def fixtureUnmatchedContext := context OccurrenceQualifiedFactReadersR65.fixtureSource
  OccurrenceQualifiedFactReadersR65.fixtureInventory fixtureNative
  OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixtureRoot [0]
  ProviderNativeContextR57.fixtureSearch [ProviderNativeContextR57.unmatchedCatch]
  [⟨.source 402,.source 305,.source 7⟩]
  {ProviderNativeContextR57.fixtureSelection with declaration := .source 305}
  ProviderNativeContextR57.fixtureProvider

theorem finite_known_unmatched_preserves_occurrences :
    InternalPermissionIncidenceR45.extract fixtureUnmatchedContext.internalInputs
      fixtureUnmatchedContext.internalQuery fixtureUnmatchedContext.internalProbe = some fixtureUnmatchedContext.internal ∧
    AuthenticatedResidualConsumerR49.IdentityReads fixtureUnmatchedContext ∧
    AuthenticatedResidualConsumerR49.classifyIdentity fixtureUnmatchedContext = .knownUnmatched ∧
    AuthenticatedResidualConsumerR49.authenticate fixtureUnmatchedContext = false ∧
    AuthenticatedResidualConsumerR49.publish fixtureUnmatchedContext
      [.effectAtom (.effectAtom 1 (.annotationMember 0 0)),.effectAtom (.effectAtom 1 (.contribution 8)),
       .effectAtom (.effectAtom 1 (.annotationMember 0 0))] (.effectRow (.effectRow 1 7)) =
      some [(.effectAtom (.effectAtom 1 (.annotationMember 0 0)),.effectRow (.effectRow 1 7)),
       (.effectAtom (.effectAtom 1 (.contribution 8)),.effectRow (.effectRow 1 7)),
       (.effectAtom (.effectAtom 1 (.annotationMember 0 0)),.effectRow (.effectRow 1 7))] := by decide

theorem finite_same_key_and_foreign_root_store_rejected :
    internalRoot OccurrenceQualifiedFactReadersR65.fixtureSource
      {OccurrenceQualifiedFactReadersR65.fixtureInventory with edges :=
        OccurrenceQualifiedFactReadersR65.fixtureInventory.edges ++ [OccurrenceQualifiedFactReadersR65.fixtureFirst]}
      fixtureNative OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot OccurrenceQualifiedFactReadersR65.fixtureSource
      {OccurrenceQualifiedFactReadersR65.fixtureInventory with edges :=
        OccurrenceQualifiedFactReadersR65.fixtureInventory.edges ++ [OccurrenceQualifiedFactReadersR65.fixtureLambdaEdge]}
      fixtureNative OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot OccurrenceQualifiedFactReadersR65.fixtureSource OccurrenceQualifiedFactReadersR65.fixtureInventory
      {fixtureNative with store := 3} OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    internalRoot OccurrenceQualifiedFactReadersR65.fixtureSource OccurrenceQualifiedFactReadersR65.fixtureInventory
      {fixtureNative with origins := fixtureNative.origins.map (fun o => {o with occurrence := 101})}
      OccurrenceQualifiedFactReadersR65.fixtureInternalQuery fixturePhysical =
      .error (nativeFailure .firstEntry .missingInternal) ∧
    AuthenticatedResidualConsumerR49.authenticate
      {fixtureContext with entryQuery := {fixtureContext.entryQuery with rootRelation := 1}} = false ∧
    AuthenticatedResidualConsumerR49.publish
      {fixtureContext with entryQuery := {fixtureContext.entryQuery with rootRelation := 1}}
      [.effectAtom (.effectAtom 1 (.annotationMember 0 0))] (.effectRow (.effectRow 1 7)) = none := by
  exact ⟨rfl,rfl,rfl,rfl,by decide,by decide⟩

theorem collected_catch_reader_retained (n : Native S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (search : Search S T)
    (occurrence : Key S T) :
    (consumerInputs n inventory search).arrival.current.sourceFact (occurrence,51) =
      ProviderNativeContextR57.sourceFact n (occurrence,51) := rfl

end YulangClosure.OccurrenceQualifiedConsumerR66
