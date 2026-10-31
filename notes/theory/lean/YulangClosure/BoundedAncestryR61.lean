import YulangClosure.NativeLocalDecodeR60

/-! R61: successful-call refinement of the ordered native ancestry visitor.
Record is the seven-constructor child/parent projection of the original owned
Dependency, not a replacement for its unused port/transport/bound payload.
Pending is represented top first; each native Vec push is list cons.
Allocation outcomes are per invocation. No single policy is claimed to simulate
arbitrary allocator histories, and actual Rust-to-Run extraction remains open. -/
namespace YulangClosure.BoundedAncestryR61


open ProviderNativeContextR57 ReachedSlotSearchR58

inductive Record where
  | derived (child parent : Nat)
  | functionPort (child parent : Nat)
  | tuplePort (child parent : Nat)
  | recordPort (child parent : Nat)
  | variantPort (child parent : Nat)
  | replay (child lower upper : Nat)
  | transport (child parent : Nat)

def child : Record → Nat
  | .derived c _ | .functionPort c _ | .tuplePort c _ | .recordPort c _
  | .variantPort c _ | .replay c _ _ | .transport c _ => c

def parents : Record → List Nat
  | .derived _ p | .functionPort _ p | .tuplePort _ p | .recordPort _ p
  | .variantPort _ p | .transport _ p => [p]
  | .replay _ lower upper => [lower,upper]

def selected (r : Record) (c : Nat) : List Nat :=
  if child r = c then parents r else []
def edges (records : List Record) : List (Nat × Nat) :=
  records.flatMap (fun r => (parents r).map (fun p => (p,child r)))
def dependencyRows (state : Nat) (records : List Record) : List Dependency :=
  records.flatMap (fun r => (parents r).map (fun p => ⟨state,p,child r⟩))

/-- Construct existing R57 fields from one indexed source relation payload
vector and the entire ordered source dependency projection. Other owner fields
and all relation endpoints are retained. Pointer-to-Nat extraction is not proved. -/
def native {S T : Type} (base : Native S T) (records : List Record) : Native S T :=
  { base with
    relations := base.relations.zipIdx.map (fun (r,i) => { r with state := base.state, index := i })
    dependencies := dependencyRows base.state records }

variable {S T : Type} [DecidableEq S] [DecidableEq T]

theorem filter_true (xs : List A) : xs.filter (fun _ => true) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.filter_cons, ite_true, ih]

omit [DecidableEq S] [DecidableEq T] in
theorem native_relation_count (base : Native S T) (records : List Record) :
    (native base records).relations.length = base.relations.length := by
  simp [native]

theorem native_live (base : Native S T) (records : List Record) :
    (current (native base records)).liveRelations = List.range base.relations.length := by
  simp only [current,native,List.filter_map,List.map_map]
  simp only [Function.comp_def,decide_true]
  rw [filter_true]
  exact by simpa only [List.range_eq_range'] using List.zipIdx_map_snd 0 base.relations

theorem native_edges (base : Native S T) (records : List Record) :
    (current (native base records)).dependencies = edges records := by
  simp only [current,dependencies,native,dependencyRows,edges,List.filter_flatMap,
    List.filter_map,List.map_flatMap,List.map_map]
  simp only [Function.comp_def,decide_true,filter_true]

theorem selected_is_retained (records : List Record) (r : Record) (c p : Nat)
    (member : r ∈ records) (chosen : p ∈ selected r c) : (p,c) ∈ edges records := by
  unfold selected at chosen
  split at chosen
  · rename_i same
    subst c
    exact List.mem_flatMap.mpr ⟨r,member,List.mem_map.mpr ⟨p,chosen,rfl⟩⟩
  · simp at chosen

theorem replay_both_parents (records : List Record) (c lower upper : Nat)
    (member : Record.replay c lower upper ∈ records) :
    (lower,c) ∈ edges records ∧ (upper,c) ∈ edges records := by
  constructor
  · exact selected_is_retained records _ c lower member (by simp [selected,child,parents])
  · exact selected_is_retained records _ c upper member (by simp [selected,child,parents])

inductive Path (records : List Record) (count : Nat) : Nat → Nat → Prop where
  | refl {r} : r < count → Path records count r r
  | step {r c target} : r < count → (r,c) ∈ edges records →
      Path records count c target → Path records count r target

theorem path_to_existing (base : Native S T) (records : List Record) (root target : Nat)
    (path : Path records base.relations.length root target) :
    CurrentEmissionOwnershipR47.RelationPath (current (native base records)) root target := by
  induction path with
  | refl live =>
    apply CurrentEmissionOwnershipR47.RelationPath.refl
    rw [native_live]
    exact List.mem_range.mpr live
  | step live edge _ ih =>
    apply CurrentEmissionOwnershipR47.RelationPath.step _ _ ih
    · rw [native_live]
      exact List.mem_range.mpr live
    · rw [native_edges]
      exact edge

theorem path_has_checked_witness (base : Native S T) (records : List Record) (root target : Nat)
    (path : Path records base.relations.length root target) :
    ∃ witness, CurrentEmissionOwnershipR47.ancestryCheck
      (current (native base records)) root witness target = true := by
  induction path with
  | refl live =>
    exact ⟨[],by simp [CurrentEmissionOwnershipR47.ancestryCheck,native_live,live]⟩
  | @step r c target live edge _ ih =>
    rcases ih with ⟨witness,checked⟩
    exact ⟨c::witness,by simp [CurrentEmissionOwnershipR47.ancestryCheck,native_live,
      native_edges,live,edge,checked]⟩

inductive AllocationSite where | initialPending | initialSeen | parentPush
inductive WorkSite where | pop | dependency
inductive Error where
  | invalidQuery | oversizedInventory
  | allocation (site : AllocationSite)
  | overflow (site : WorkSite) | workLimit (site : WorkSite)
  | invalidChild | invalidParent | exhausted
structure Budget where
  work : Nat
  usizeMax : Nat
def nativeBudget : Budget := ⟨65536,2^64-1⟩
structure State where
  resource : Resource
  pending : List Nat
  seen : List Nat

def tick (budget : Budget) (site : WorkSite) (r : Resource) : Except Error Resource :=
  if r.work+1 ≤ budget.usizeMax then
    if r.work+1 ≤ budget.work then .ok {r with work := r.work+1}
    else .error (.workLimit site)
  else .error (.overflow site)

def allocate (site : AllocationSite) (_amount : Nat) (r : Resource) : Except Error Resource :=
  match r.allocations with
  | true::rest => .ok {r with allocations := rest}
  | _ => .error (.allocation site)

/-- Source order: both query indices, then unconditional inventory cap, then
pending reservation followed by seen reservation; independent visits starts 0. -/
def start (count descendant ancestor : Nat) (allocations : List Bool) : Except Error State := do
  if ¬ (descendant < count ∧ ancestor < count) then .error .invalidQuery
  else if count > 65536 then .error .oversizedInventory
  else
    let r ← allocate .initialPending (min count 65536) ⟨0,allocations⟩
    let r ← allocate .initialSeen (min count 65536) r
    .ok ⟨r,[descendant],[]⟩

/-- Parent index validation precedes visited suppression; successful Vec push
is cons. Replay lower is pushed before upper, therefore upper is popped first. -/
def enqueue (count : Nat) (seen : List Nat) : List Nat → State → Except Error State
  | [],s => .ok s
  | p::ps,s => do
      if p ≥ count then .error .invalidParent
      else if p ∈ seen then enqueue count seen ps s
      else
        let r ← allocate .parentPush 1 s.resource
        enqueue count seen ps {s with resource := r, pending := p::s.pending}

/-- Every dependency record costs one visit, including nonmatching records.
The full original vector is scanned once per unseen, nonterminal popped node. -/
def scan (budget : Budget) (count c : Nat) : List Record → State → Except Error State
  | [],s => .ok s
  | r::rs,s => do
      let resource ← tick budget .dependency s.resource
      let s ← enqueue count s.seen (selected r c) {s with resource}
      scan budget count c rs s

inductive Outcome where
  | next (state : State) | success (resource : Resource) | failure (error : Error)

def step (budget : Budget) (count ancestor : Nat) (records : List Record) (s : State) : Outcome :=
  match s.pending with
  | [] => .failure .exhausted
  | c::rest =>
    match tick budget .pop s.resource with
    | .error error => .failure error
    | .ok resource =>
      if c = ancestor then .success resource
      else if c ∈ s.seen then .next {s with resource, pending := rest}
      else if c ≥ count then .failure .invalidChild
      else match scan budget count c records ⟨resource,rest,c::s.seen⟩ with
        | .error error => .failure error
        | .ok next => .next next

inductive Run (budget : Budget) (count ancestor : Nat) (records : List Record) : State → Outcome → Prop where
  | done {s out} : step budget count ancestor records s = out →
      (∀ next, out ≠ .next next) → Run budget count ancestor records s out
  | more {s next out} : step budget count ancestor records s = .next next →
      Run budget count ancestor records next out → Run budget count ancestor records s out

/-- Meta fuel is only an evaluator bound, not a new native failure. -/
def evaluate (fuel : Nat) (budget : Budget) (count ancestor : Nat) (records : List Record)
    (s : State) : Option Outcome :=
  match fuel with
  | 0 => none
  | fuel+1 => match step budget count ancestor records s with
    | .next next => evaluate fuel budget count ancestor records next
    | .success r => some (.success r)
    | .failure error => some (.failure error)

def Frontier (records : List Record) (count descendant : Nat) (s : State) : Prop :=
  ∀ p ∈ s.pending, Path records count p descendant

/-- Resource changes do not manufacture graph evidence. -/
theorem frontier_resource (records : List Record) (count descendant : Nat) (s : State)
    (resource : Resource) (front : Frontier records count descendant s) :
    Frontier records count descendant {s with resource} := front

theorem enqueue_preserves (records : List Record) (count descendant c : Nat)
    (ps : List Nat) (seen : List Nat) (s next : State)
    (parentEdges : ∀ p ∈ ps, (p,c) ∈ edges records)
    (childPath : Path records count c descendant)
    (front : Frontier records count descendant s)
    (success : enqueue count seen ps s = .ok next) :
    Frontier records count descendant next := by
  induction ps generalizing s with
  | nil => simp [enqueue] at success; subst next; exact front
  | cons p ps ih =>
    simp only [enqueue] at success
    split at success
    · contradiction
    · rename_i valid
      split at success
      · exact ih s (fun x hx => parentEdges x (by simp [hx])) front success
      · cases allocation : allocate .parentPush 1 s.resource with
        | error error => simp [allocation,Bind.bind,Except.bind] at success
        | ok resource =>
          simp only [allocation,Bind.bind,Except.bind] at success
          apply ih _ (fun x hx => parentEdges x (by simp [hx])) _ success
          intro x member
          simp only [List.mem_cons] at member
          rcases member with same | member
          · subst x
            exact .step (by omega) (parentEdges p (by simp)) childPath
          · exact front x member

theorem scan_preserves (records remaining : List Record) (budget : Budget)
    (count descendant c : Nat) (s next : State)
    (subset : ∀ r ∈ remaining, r ∈ records)
    (childPath : Path records count c descendant)
    (front : Frontier records count descendant s)
    (success : scan budget count c remaining s = .ok next) :
    Frontier records count descendant next := by
  induction remaining generalizing s with
  | nil => simp [scan] at success; subst next; exact front
  | cons r rs ih =>
    simp only [scan] at success
    cases charged : tick budget .dependency s.resource with
    | error error => simp [charged,Bind.bind,Except.bind] at success
    | ok resource =>
      simp only [charged,Bind.bind,Except.bind] at success
      cases queued : enqueue count s.seen (selected r c) {s with resource} with
      | error error => simp [queued] at success
      | ok middle =>
        simp only [queued] at success
        apply ih middle (fun r hr => subset r (by simp [hr])) _ success
        exact enqueue_preserves records count descendant c _ _ {s with resource} middle
          (fun p hp => selected_is_retained records r c p (subset r (by simp)) hp)
          childPath (frontier_resource records count descendant s resource front) queued

def SoundOutcome (records : List Record) (count descendant ancestor : Nat) : Outcome → Prop
  | .next next => Frontier records count descendant next
  | .success _ => Path records count ancestor descendant
  | .failure _ => True

theorem step_sound (budget : Budget) (count descendant ancestor : Nat)
    (records : List Record) (s : State) (front : Frontier records count descendant s) :
    SoundOutcome records count descendant ancestor (step budget count ancestor records s) := by
  cases pending : s.pending with
  | nil => simp only [step,pending,SoundOutcome]
  | cons c rest =>
    simp only [step,pending]
    cases charged : tick budget .pop s.resource with
    | error error => simp only [SoundOutcome]
    | ok resource =>
      dsimp only
      split
      · rename_i target
        subst c
        exact front ancestor (by simp [pending])
      · split
        · intro p hp
          exact front p (by simp [pending,hp])
        · split
          · trivial
          · cases scanned : scan budget count c records ⟨resource,rest,c::s.seen⟩ with
            | error error => trivial
            | ok next =>
              apply scan_preserves records records budget count descendant c _ next
                (fun _ h => h) (front c (by simp [pending])) _ scanned
              intro p hp
              exact front p (by simp only [pending,List.mem_cons]; exact Or.inr hp)

theorem successful_run_ancestry (budget : Budget) (count descendant ancestor : Nat)
    (records : List Record) (s : State) (resource : Resource)
    (front : Frontier records count descendant s)
    (run : Run budget count ancestor records s (.success resource)) :
    Path records count ancestor descendant := by
  generalize finalEq : Outcome.success resource = final at run
  induction run with
  | done transition _ =>
    have sound := step_sound budget count descendant ancestor records _ front
    rw [transition,←finalEq] at sound
    exact sound
  | more transition _ ih =>
    have sound := step_sound budget count descendant ancestor records _ front
    rw [transition] at sound
    exact ih sound finalEq

theorem start_frontier (records : List Record) (count descendant ancestor : Nat)
    (allocations : List Bool) (s : State)
    (started : start count descendant ancestor allocations = .ok s) :
    Frontier records count descendant s := by
  unfold start at started
  split at started
  · contradiction
  · rename_i valid
    split at started
    · contradiction
    · cases pending : allocate .initialPending (min count 65536) ⟨0,allocations⟩ with
      | error error => simp [pending,Bind.bind,Except.bind] at started
      | ok r =>
        simp only [pending,Bind.bind,Except.bind] at started
        cases seen : allocate .initialSeen (min count 65536) r with
        | error error => simp [seen] at started
        | ok resource =>
          simp only [seen,Except.ok.injEq] at started
          subst s
          intro p hp
          simp only [List.mem_singleton] at hp
          subst p
          exact .refl (by
            by_cases live : descendant < count
            · exact live
            · exact False.elim (valid (fun indices => live indices.1)))

theorem initial_success_refines_directed_retained_ancestry
    (base : Native S T) (records : List Record) (budget : Budget)
    (descendant ancestor : Nat) (allocations : List Bool) (s : State) (resource : Resource)
    (started : start base.relations.length descendant ancestor allocations = .ok s)
    (run : Run budget base.relations.length ancestor records s (.success resource)) :
    CurrentEmissionOwnershipR47.RelationPath (current (native base records)) ancestor descendant ∧
    ∃ witness, CurrentEmissionOwnershipR47.ancestryCheck
      (current (native base records)) ancestor witness descendant = true := by
  have path := successful_run_ancestry budget base.relations.length descendant ancestor records s resource
    (start_frontier records _ _ _ _ _ started) run
  exact ⟨path_to_existing base records ancestor descendant path,
    path_has_checked_witness base records ancestor descendant path⟩

theorem evaluation_success_is_run (fuel : Nat) (budget : Budget)
    (count ancestor : Nat) (records : List Record) (s : State) (resource : Resource)
    (evaluated : evaluate fuel budget count ancestor records s = some (.success resource)) :
    Run budget count ancestor records s (.success resource) := by
  induction fuel generalizing s with
  | zero => simp [evaluate] at evaluated
  | succ fuel ih =>
    simp only [evaluate] at evaluated
    cases transition : step budget count ancestor records s with
    | failure error => simp [transition] at evaluated
    | success result =>
      simp only [transition,Option.some.injEq,Outcome.success.injEq] at evaluated
      subst result
      exact .done transition (by intro next h; cases h)
    | next next =>
      simp only [transition] at evaluated
      exact .more transition (ih next evaluated)

/-- The actual record argument is kept explicit (not a successful-path table). -/
def call (records : List Record) (fuel : Nat) (budget : Budget)
    (count descendant ancestor : Nat) (allocations : List Bool) : Option Outcome :=
  match start count descendant ancestor allocations with
  | .error error => some (.failure error)
  | .ok s => evaluate fuel budget count ancestor records s

theorem call_success_constructs_witness (base : Native S T) (records : List Record)
    (fuel : Nat) (budget : Budget) (descendant ancestor : Nat)
    (allocations : List Bool) (resource : Resource)
    (success : call records fuel budget base.relations.length descendant ancestor allocations =
      some (.success resource)) :
    CurrentEmissionOwnershipR47.RelationPath (current (native base records)) ancestor descendant ∧
    ∃ witness, CurrentEmissionOwnershipR47.ancestryCheck
      (current (native base records)) ancestor witness descendant = true := by
  unfold call at success
  cases started : start base.relations.length descendant ancestor allocations with
  | error error => simp [started] at success
  | ok s =>
    simp only [started] at success
    exact initial_success_refines_directed_retained_ancestry base records budget descendant ancestor
      allocations s resource started (evaluation_success_is_run fuel budget _ _ _ _ _ success)

def errorFailure : Error → Failure
  | .invalidQuery | .invalidChild | .invalidParent => nativeFailure .relationIndex .invalidRelation
  | .oversizedInventory => ⟨.relationCount,.searchLimit,.workLimit⟩
  | .allocation _ => ⟨.laterAncestry,.searchLimit,.allocation⟩
  | .overflow _ => ⟨.laterAncestry,.searchLimit,.overflow⟩
  | .workLimit _ => ⟨.laterAncestry,.searchLimit,.workLimit⟩
  | .exhausted => nativeFailure .laterAncestry .missingUseAncestry
structure Schedule where
  fuel : Nat
  allocations : List Bool

/-- One selected resource schedule per query, not an equivalence with arbitrary
allocator histories. The uncompleted meta observation is unavailable. Exact
native failure ordering remains visible in `call`, before this API erasure. -/
def callback (records : List Record) (count : Nat)
    (schedule : Nat → Nat → Schedule) (descendant ancestor : Nat) : Except Failure Unit :=
  match call records (schedule descendant ancestor).fuel nativeBudget count descendant ancestor
      (schedule descendant ancestor).allocations with
  | some (.success _) => .ok ()
  | some (.failure error) => .error (errorFailure error)
  | _ => .error ⟨.laterAncestry,.searchLimit,.workLimit⟩

def policy (base : Native S T) (records : List Record)
    (internal : Physical T → Except Failure (InternalReceipt T))
    (schedule : Nat → Nat → Schedule) : NativeLocalDecodeR60.Policy T :=
  ⟨internal,callback records base.relations.length schedule⟩

theorem callback_success_has_ancestry (base : Native S T) (records : List Record)
    (schedule : Nat → Nat → Schedule) (descendant ancestor : Nat)
    (success : callback records base.relations.length schedule descendant ancestor = .ok ()) :
    CurrentEmissionOwnershipR47.RelationPath (current (native base records)) ancestor descendant ∧
    ∃ witness, CurrentEmissionOwnershipR47.ancestryCheck
      (current (native base records)) ancestor witness descendant = true := by
  unfold callback at success
  cases observed : call records (schedule descendant ancestor).fuel nativeBudget
      base.relations.length descendant ancestor (schedule descendant ancestor).allocations with
  | none => simp [observed] at success
  | some out =>
    cases out with
    | next next => simp [observed] at success
    | failure error => simp [observed] at success
    | success resource =>
      exact call_success_constructs_witness base records _ _ _ _ _ resource observed

theorem constructed_ancestry_read_is_sound (base : Native S T) (records : List Record)
    (internal : Physical T → Except Failure (InternalReceipt T))
    (schedule : Nat → Nat → Schedule) (descendant ancestor : Nat)
    (success : ancestryRead
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      descendant ancestor = .ok ()) :
    CurrentEmissionOwnershipR47.RelationPath (current (native base records)) ancestor descendant ∧
    ∃ witness, CurrentEmissionOwnershipR47.ancestryCheck
      (current (native base records)) ancestor witness descendant = true := by
  unfold ancestryRead at success
  split at success
  · split at success
    · exact callback_success_has_ancestry base records schedule descendant ancestor success
    · contradiction
  · contradiction

/-- Existing successful candidate converse/consumer theorem, now on the exact
same Native constructor and a computed, sound successful-call ancestry policy.
The Internal primitive and outer successful Run/Checked remain explicit. -/
theorem successful_candidates_with_constructed_ancestry (base : Native S T)
    (records : List Record) (search : Search S T)
    (internal : Physical T → Except Failure (InternalReceipt T))
    (schedule : Nat → Nat → Schedule) (q : Query) (limits : Limits) (r : Resource)
    (results : List (Branch S T))
    (run : ReachedSlotSearchR58.Run
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T)
    (checked : Checked
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule)) q goal)
    (terminal : goal.endpoint = q.target) :
    goal ∈ results ∧
    AuthenticatedResidualConsumerR49.pathCheck (inputs (native base records) search)
      (encodedEndpoint (NativeLocalDecodeR60.constructedReaders (native base records)
        (policy base records internal schedule)) q.root)
      (goal.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint (NativeLocalDecodeR60.constructedReaders (native base records)
        (policy base records internal schedule)) q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival (inputs (native base records) search)
      (encodedEndpoint (NativeLocalDecodeR60.constructedReaders (native base records)
        (policy base records internal schedule)) q.target)
      (encodedEndpoint (NativeLocalDecodeR60.constructedReaders (native base records)
        (policy base records internal schedule)) q.root) :=
  NativeLocalDecodeR60.complete_candidates_on_constructed_inputs (native base records) search
    (policy base records internal schedule) q limits r results run goal checked terminal


omit [DecidableEq S] [DecidableEq T] in
theorem native_preserves_physical_owner (base : Native S T) (records : List Record) :
    (native base records).state = base.state ∧
    (native base records).effectRows = base.effectRows ∧
    (native base records).views = base.views ∧
    (native base records).emissions = base.emissions ∧
    (native base records).admissions = base.admissions ∧
    (native base records).facts = base.facts := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

omit [DecidableEq S] [DecidableEq T] in
theorem native_relation_payloads (base : Native S T) (records : List Record) :
    (native base records).relations.map (fun r => (r.lower,r.upper)) =
      base.relations.map (fun r => (r.lower,r.upper)) := by
  simp only [native,List.map_map,Function.comp_def]
  have same := congrArg (List.map (fun r : Relation T => (r.lower,r.upper)))
    (List.zipIdx_map_fst 0 base.relations)
  simpa only [List.map_map,Function.comp_def] using same

/- Explicit coordinate equations suffice to reuse an already constructed
Native verbatim. These are inventory/index equations, not ancestry assumptions. -/
omit [DecidableEq S] [DecidableEq T] in
theorem native_eq_existing_of_owner_coordinates (base : Native S T) (records : List Record)
    (relationCoordinates : base.relations.zipIdx.map
      (fun (r,i) => { r with state := base.state, index := i }) = base.relations)
    (dependencyCoordinates : dependencyRows base.state records = base.dependencies) :
    native base records = base := by
  simp only [native,relationCoordinates,dependencyCoordinates]

/-- A proof observer cannot turn an actual failure or missing observation into
success. Only the success constructor is accepted by the policy callback. -/
theorem no_failed_call_is_success (records : List Record) (fuel : Nat) (budget : Budget)
    (count descendant ancestor : Nat) (allocations : List Bool) (error : Error)
    (failed : call records fuel budget count descendant ancestor allocations = some (.failure error)) :
    ∀ resource, call records fuel budget count descendant ancestor allocations ≠ some (.success resource) := by
  intro resource success
  rw [failed] at success
  cases success

def fourReservations : List Bool := [true,true,true,true]
def threeReservations : List Bool := [true,true,true]
def replayFixture : List Record := [.replay 2 0 1]

theorem replay_source_parent_order : selected (.replay 2 0 1) 2 = [0,1] := rfl

theorem replay_lifo_upper_first :
    enqueue 3 [2] [0,1] ⟨⟨0,[true,true]⟩,[],[2]⟩ =
      .ok ⟨⟨0,[]⟩,[1,0],[2]⟩ := rfl

theorem both_replay_parents_are_reached :
    call replayFixture 5 nativeBudget 3 2 1 fourReservations = some (.success ⟨3,[]⟩) ∧
    call replayFixture 5 nativeBudget 3 2 0 fourReservations = some (.success ⟨5,[]⟩) := by
  exact ⟨rfl,rfl⟩

theorem omitting_either_replay_parent_loses_success :
    call [.derived 2 1] 5 nativeBudget 3 2 0 threeReservations = some (.failure .exhausted) ∧
    call [.derived 2 0] 5 nativeBudget 3 2 1 threeReservations = some (.failure .exhausted) := by
  exact ⟨rfl,rfl⟩

theorem directed_edge_cannot_be_reversed :
    call [.derived 2 0] 5 nativeBudget 3 2 0 threeReservations = some (.success ⟨3,[]⟩) ∧
    call [.derived 2 0] 5 nativeBudget 3 0 2 [true,true] = some (.failure .exhausted) := by
  exact ⟨rfl,rfl⟩

theorem query_index_precedes_inventory_and_allocation :
    start 65537 65537 0 [] = .error .invalidQuery ∧
    start 65537 0 0 [] = .error .oversizedInventory := by
  exact ⟨rfl,rfl⟩

theorem oversized_reflexive_is_unavailable :
    call [] 1 nativeBudget 65537 0 0 [true,true] = some (.failure .oversizedInventory) := rfl

theorem initial_reservation_order :
    start 1 0 0 [] = .error (.allocation .initialPending) ∧
    start 1 0 0 [true] = .error (.allocation .initialSeen) := by
  exact ⟨rfl,rfl⟩

theorem same_query_different_reservation_outcomes :
    call [] 1 nativeBudget 1 0 0 [] = some (.failure (.allocation .initialPending)) ∧
    call [] 1 nativeBudget 1 0 0 [true,true] = some (.success ⟨1,[]⟩) := by
  exact ⟨rfl,rfl⟩

theorem invalid_parent_checked_before_seen :
    step nativeBudget 3 0 [.derived 2 3] ⟨⟨0,[]⟩,[2],[3]⟩ =
      .failure .invalidParent := rfl

theorem unreachable_invalid_parent_is_not_globally_rejected :
    call [.derived 0 99] 1 nativeBudget 1 0 0 [true,true] = some (.success ⟨1,[]⟩) ∧
    call [.derived 1 99] 3 nativeBudget 2 1 0 [true,true] = some (.failure .invalidParent) := by
  exact ⟨rfl,rfl⟩

theorem cycle_exhausts_without_false_ancestor :
    call [.derived 2 1,.transport 1 2] 5 nativeBudget 3 2 0 threeReservations =
      some (.failure .exhausted) := rfl

theorem duplicate_unseen_parent_preserves_both_pushes :
    enqueue 3 [2] [1,1] ⟨⟨0,[true,true]⟩,[],[2]⟩ =
      .ok ⟨⟨0,[]⟩,[1,1],[2]⟩ := rfl

theorem duplicate_record_can_change_reservation_failure :
    call [.derived 2 1] 3 nativeBudget 3 2 1 threeReservations = some (.success ⟨3,[]⟩) ∧
    call [.derived 2 1,.derived 2 1] 3 nativeBudget 3 2 1 threeReservations =
      some (.failure (.allocation .parentPush)) := by
  exact ⟨rfl,rfl⟩

theorem record_order_changes_lifo_bounded_outcome :
    call [.derived 2 0,.derived 2 1] 5 ⟨4,100⟩ 3 2 1 fourReservations =
      some (.success ⟨4,[]⟩) ∧
    call [.derived 2 1,.derived 2 0] 5 ⟨4,100⟩ 3 2 1 fourReservations =
      some (.failure (.workLimit .dependency)) := by
  exact ⟨rfl,rfl⟩

theorem pop_work_checked_before_reflexive_acceptance :
    step nativeBudget 1 0 [] ⟨⟨65536,[]⟩,[0],[]⟩ = .failure (.workLimit .pop) := rfl

theorem overflow_precedes_work_limit :
    tick ⟨0,0⟩ .pop ⟨0,[]⟩ = .error (.overflow .pop) := rfl

theorem nonmatching_dependencies_are_charged :
    scan ⟨0,100⟩ 3 2 [.derived 1 0] ⟨⟨0,[]⟩,[],[]⟩ =
      .error (.workLimit .dependency) := rfl

theorem visited_pop_costs_work_but_does_not_rescan :
    step nativeBudget 3 0 [.derived 2 99] ⟨⟨0,[]⟩,[2],[2]⟩ =
      .next ⟨⟨1,[]⟩,[],[2]⟩ := rfl

theorem allocation_keeps_independent_visit_count (site : AllocationSite) (amount : Nat)
    (before after : Resource) (success : allocate site amount before = .ok after) :
    after.work = before.work := by
  rcases before with ⟨work,allocations⟩
  cases allocations with
  | nil => simp [allocate] at success
  | cons b bs =>
    cases b with
    | false => simp [allocate] at success
    | true =>
      simp only [allocate,Except.ok.injEq] at success
      subst after
      rfl

theorem each_call_starts_its_own_zero_counter (count descendant ancestor : Nat)
    (allocations : List Bool) (s : State)
    (started : start count descendant ancestor allocations = .ok s) :
    s.resource.work = 0 := by
  unfold start at started
  split at started
  · contradiction
  · split at started
    · contradiction
    · cases pending : allocate .initialPending (min count 65536) ⟨0,allocations⟩ with
      | error error => simp [pending,Bind.bind,Except.bind] at started
      | ok r =>
        simp only [pending,Bind.bind,Except.bind] at started
        cases seen : allocate .initialSeen (min count 65536) r with
        | error error => simp [seen] at started
        | ok resource =>
          simp only [seen,Except.ok.injEq] at started
          subst s
          exact (allocation_keeps_independent_visit_count .initialSeen (min count 65536) r resource seen).trans
            (allocation_keeps_independent_visit_count .initialPending (min count 65536) ⟨0,allocations⟩ r pending)

/- Same previously supplied Native, once raw storage/index projection equations
are established. No semantic ancestry premise is imported. -/
theorem call_success_on_the_existing_owner (base : Native S T) (records : List Record)
    (relationCoordinates : base.relations.zipIdx.map
      (fun (r,i) => { r with state := base.state, index := i }) = base.relations)
    (dependencyCoordinates : dependencyRows base.state records = base.dependencies)
    (fuel : Nat) (budget : Budget) (descendant ancestor : Nat)
    (allocations : List Bool) (resource : Resource)
    (success : call records fuel budget base.relations.length descendant ancestor allocations =
      some (.success resource)) :
    CurrentEmissionOwnershipR47.RelationPath (current base) ancestor descendant ∧
    ∃ witness, CurrentEmissionOwnershipR47.ancestryCheck
      (current base) ancestor witness descendant = true := by
  have checked := call_success_constructs_witness base records fuel budget descendant ancestor
    allocations resource success
  rw [native_eq_existing_of_owner_coordinates base records relationCoordinates dependencyCoordinates] at checked
  exact checked

theorem record_order_changes_native_bounded_prefix :
    evaluate 5 nativeBudget 3 1 [.derived 2 0,.derived 2 1]
      ⟨⟨65532,[true,true]⟩,[2],[]⟩ = some (.success ⟨65536,[]⟩) ∧
    evaluate 5 nativeBudget 3 1 [.derived 2 1,.derived 2 0]
      ⟨⟨65532,[true,true]⟩,[2],[]⟩ = some (.failure (.workLimit .dependency)) := by
  exact ⟨rfl,rfl⟩

theorem later_entry_policy_has_directed_ancestry (base : Native S T) (records : List Record)
    (internal : Physical T → Except Failure (InternalReceipt T))
    (schedule : Nat → Nat → Schedule) (b : Branch S T) (p : Physical T)
    (root : Nat) (head : PathStep S T) (tail : List (PathStep S T))
    (success : ReachedSlotSearchR58.policy
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      .entrySearch { b with useRoot := some root, steps := head::tail } p = .ok (some root)) :
    CurrentEmissionOwnershipR47.RelationPath (current (native base records)) root p.relation := by
  simp only [ReachedSlotSearchR58.policy] at success
  cases ancestry : ancestryRead
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      p.relation root with
  | error error => simp [ancestry,Bind.bind,Except.bind] at success
  | ok answer =>
    cases answer
    exact (constructed_ancestry_read_is_sound base records internal schedule p.relation root ancestry).1

/-- First-entry Internal extraction is still a separate primitive. The checked
visitor proves the receipt's relation, without assuming it equals p.relation. -/
theorem first_entry_policy_exposes_receipt_ancestry (base : Native S T) (records : List Record)
    (internal : Physical T → Except Failure (InternalReceipt T))
    (schedule : Nat → Nat → Schedule) (b : Branch S T) (p : Physical T) (result : Option Nat)
    (success : ReachedSlotSearchR58.policy
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      .entrySearch { b with useRoot := none, steps := [] } p = .ok result) :
    ∃ receipt, internal p = .ok receipt ∧
      CurrentEmissionOwnershipR47.RelationPath (current (native base records)) receipt.useRoot receipt.relation := by
  simp only [ReachedSlotSearchR58.policy] at success
  change (do
    let receipt ← internal p
    let _ ← ancestryRead
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      receipt.relation receipt.useRoot
    if receipt.emissionIndex = p.emissionIndex ∧ receipt.admissionIndex = p.admissionIndex ∧
      receipt.slot = p.emission.physical ∧ receipt.bound = p.emission.bound
    then .ok (some receipt.useRoot)
    else .error (nativeFailure .firstEntry .boundMismatch)) = .ok result at success
  cases read : internal p with
  | error error => simp [read,Bind.bind,Except.bind] at success
  | ok receipt =>
    simp only [read,Bind.bind,Except.bind] at success
    cases ancestry : ancestryRead
        (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
        receipt.relation receipt.useRoot with
    | error error => simp [ancestry] at success
    | ok answer =>
      cases answer
      exact ⟨receipt,rfl,(constructed_ancestry_read_is_sound base records internal schedule
        receipt.relation receipt.useRoot ancestry).1⟩

theorem catch_policy_skips_the_visitor (base : Native S T) (records : List Record)
    (internal : Physical T → Except Failure (InternalReceipt T))
    (schedule : Nat → Nat → Schedule) (b : Branch S T) (p : Physical T) :
    ReachedSlotSearchR58.policy
      (NativeLocalDecodeR60.constructedReaders (native base records) (policy base records internal schedule))
      .catchSearch b p = .ok none := by
  cases b with
  | mk endpoint steps seen useRoot => cases useRoot <;> cases steps <;> rfl

end YulangClosure.BoundedAncestryR61
