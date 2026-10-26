import YulangClosure.NativeRelationInterner
import YulangClosure.NativeValueDrain

/-!
Physical relation allocation supplies the exact decoded Value-port admission
and its shared enqueue occurrence.  Context/transformer preparation uses the
already checked successful constructors.  Their physical resource trace and
the later dependency/sampling cuts retain their separate native owners.
-/
namespace YulangClosure.NativeValueRelationExecution

namespace P
export NativeValuePorts (Arena Key Child Receipt Flow Transformer Port Cursor)
end P
namespace I
export NativeRelationInterner (Native NativeHistory NativeRun Resources Result Failure)
end I
namespace D
export NativeValueDrain (State Origin Active ParentPresent Issuance Control)
end D

open NativeContextExpansion (Expr)

/-- The actual complete relation store and the successful preparatory tables.
No chosen decoded relation vector is a field. -/
structure Store where
  native : I.Native
  contexts : List Expr
  transformers : List P.Transformer

def Store.arena (store : Store) : P.Arena :=
  store.native.store.arena store.contexts store.transformers

def Store.tables (store : Store) (arena : P.Arena) : Store :=
  {store with contexts := arena.contexts, transformers := arena.transformers}

def prepare (arena : P.Arena) (views : Nat → Option (Option Nat))
    (qv qe : Nat → Nat) (parent : P.Key) (post : Nat) (child : P.Child) :
    Option (P.Arena × P.Key) := do
  let pair := child.task.rename qv qe
  let weight ← NativeValuePorts.sourceWeight views pair
  let context := NativeValuePorts.buildContext arena weight post child.port.swaps
  let (flowArena, flow) ← NativeValuePorts.buildFlow context.1 parent child.port
  some (flowArena, ⟨pair, context.2, parent.sources, flow⟩)

theorem context_keeps_relation_vector (arena : P.Arena) (weight : Option Nat)
    (post : Nat) (swap : Bool) :
    (NativeValuePorts.buildContext arena weight post swap).1.relations = arena.relations := by
  cases weight <;>
    simp only [NativeValuePorts.buildContext] <;> split <;> rfl

theorem transformer_keeps_relation_vector (arena : P.Arena) (transformer : P.Transformer) :
    (arena.transformer transformer).1.relations = arena.relations := by
  unfold NativeValuePorts.Arena.transformer
  split <;> rfl

theorem flow_keeps_relation_vector {arena after : P.Arena} {parent : P.Key}
    {port : P.Port} {flow : P.Flow}
    (computed : NativeValuePorts.buildFlow arena parent port = some (after, flow)) :
    after.relations = arena.relations := by
  cases port with
  | tuple | record | variant => cases computed; rfl
  | function field =>
      by_cases zero : parent.flow.transformer = 0
      · cases hd : parent.flow.demand with
        | none => simp only [NativeValuePorts.buildFlow, zero, ne_eq,
            not_true_eq_false, ↓reduceIte, hd] at computed; cases computed; rfl
        | some demand =>
            by_cases genuine : NativeValuePorts.genuineDemand parent demand
            · simp only [NativeValuePorts.buildFlow, zero, ne_eq, not_true_eq_false,
                ↓reduceIte, hd, genuine] at computed
              cases field <;> cases computed
              · rfl
              · exact transformer_keeps_relation_vector _ _
              · exact transformer_keeps_relation_vector _ _
              · rfl
            · simp [NativeValuePorts.buildFlow, zero, hd, genuine] at computed
      · simp [NativeValuePorts.buildFlow, zero] at computed

theorem prepared_keeps_relation_vector {arena prepared : P.Arena}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent key : P.Key} {post : Nat} {child : P.Child}
    (computed : prepare arena views qv qe parent post child = some (prepared, key)) :
    prepared.relations = arena.relations := by
  unfold prepare at computed
  obtain ⟨weight, _, more⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨⟨after, flow⟩, built, same⟩ := Option.bind_eq_some_iff.mp more
  cases same
  exact (flow_keeps_relation_vector built).trans (context_keeps_relation_vector _ _ _ _)

def receipt (parent key : P.Key) (child : P.Child) (derived : Bool) (id : Nat) : P.Receipt :=
  ⟨parent, key, id, child.port, derived⟩

theorem prepared_admission {arena prepared : P.Arena}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent key : P.Key} {post : Nat} {child : P.Child} (derived : Bool)
    (computed : prepare arena views qv qe parent post child = some (prepared, key))
    (allowed : NativeValuePorts.Allowed key) :
    NativeValuePorts.admit arena views qv qe parent post derived child =
      some ((prepared.relation key).1, receipt parent key child derived (prepared.relation key).2) := by
  unfold prepare at computed
  obtain ⟨weight, weightAt, more⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨⟨after, flow⟩, built, same⟩ := Option.bind_eq_some_iff.mp more
  cases same
  simp [NativeValuePorts.admit, weightAt, built, allowed, receipt]

theorem prepared_physical_tables {store : Store} {prepared : P.Arena}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent key : P.Key} {post : Nat} {child : P.Child}
    (computed : prepare store.arena views qv qe parent post child = some (prepared, key)) :
    (store.tables prepared).arena = prepared := by
  have relations := prepared_keeps_relation_vector computed
  cases prepared
  simp only [Store.tables, Store.arena, NativeRelationInterner.Store.arena] at relations ⊢
  cases relations
  rfl

/-- This event is the physical relation call AFTER successful Context/Flow
preparation. Both successful and failed calls retain their actual output store. -/
def allocate (store : Store) (resources : I.Resources) (key : P.Key) : Store × I.Result :=
  let actual := store.native.call resources key
  ({store with native := actual.1}, actual.2)

theorem allocation_history (store : Store) (resources : I.Resources) (key : P.Key)
    (history : I.NativeHistory store.native) :
    I.NativeHistory (allocate store resources key).1.native :=
  .commit history (.call (.nil _) resources key)

theorem allocation_exact {store after : Store} (history : I.NativeHistory store.native)
    {resources : I.Resources} {key : P.Key} {id : Nat}
    (computed : allocate store resources key = (after, .ok id)) :
    NativeValuePorts.Allowed key ∧ after.native.store.readback id = some key ∧
    store.arena.relation key = (after.arena, id) := by
  have success : (store.native.call resources key).2 = .ok id := congrArg Prod.snd computed
  have exact := NativeRelationInterner.native_ok_refines_arena history success
    store.contexts store.transformers
  have state := congrArg Prod.fst computed
  change {store with native := (store.native.call resources key).1} = after at state
  rw [← state]
  exact ⟨exact.1, exact.2.2.1, exact.2.2.2⟩

/-- No selected output arena, ID-reflection axiom or child-typing assumption
is needed. The raw native result supplies every field of the original port
receipt, with exactly the same relation ID and the same prepared tables. -/
theorem physical_relation_constructs_admission
    {store after : Store} (history : I.NativeHistory store.native)
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent key : P.Key} {post : Nat} {child : P.Child} {derived : Bool}
    {prepared : P.Arena} {resources : I.Resources} {id : Nat}
    (preparation : prepare store.arena views qv qe parent post child = some (prepared, key))
    (computed : allocate (store.tables prepared) resources key = (after, .ok id)) :
    NativeValuePorts.admit store.arena views qv qe parent post derived child =
      some (after.arena, receipt parent key child derived id) ∧
    I.NativeHistory after.native ∧ after.native.store.readback id = some key ∧
    NativeValuePorts.AdmissionResult after.arena views qv qe parent post derived child
      (receipt parent key child derived id) := by
  have actual := allocation_exact (store := store.tables prepared) history computed
  have projected := actual.2.2
  rw [prepared_physical_tables preparation] at projected
  have pure := prepared_admission derived preparation actual.1
  rw [projected] at pure
  refine ⟨pure, ?_, actual.2.1, (NativeValuePorts.admit_constructs pure).2⟩
  have reachable := allocation_history (store.tables prepared) resources key history
  simpa only [computed] using reachable

/-- Actual successful ScopeInventory work incurred by preparatory scope
transformer allocation. It is separate from the relation call's own charge.
Its measured amount and reservation flags remain native resource inputs. -/
structure Funding extends I.Resources where
  preparationWork : Nat := 0

def inventory (store : Store) (amount maximum : Nat) : Option Store :=
  if store.native.store.workUsed + amount ≤ maximum ∧
      store.native.store.workUsed + amount ≤ 65536 then
    some {store with native := store.native.inventory amount}
  else none

theorem inventory_exact {store after : Store} {amount maximum : Nat}
    (history : I.NativeHistory store.native)
    (computed : inventory store amount maximum = some after) :
    after.arena = store.arena ∧ I.NativeHistory after.native ∧
    after.native.store.workUsed = store.native.store.workUsed + amount := by
  unfold inventory at computed
  split at computed
  · rename_i guards
    cases computed
    exact ⟨rfl, .commit history (.inventory (.nil _) amount maximum guards.1 guards.2), rfl⟩
  · cases computed

/-- Preparation failure is outside this successful-table projection. Once the
physical relation call is reached, its failed output is retained explicitly;
an unavailable relation is never converted into a successful port receipt. -/
def admit (store : Store) (resources : Funding)
    (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : P.Key) (post : Nat) (derived : Bool) (child : P.Child) :
    Option (Store × Except I.Failure P.Receipt) := do
  let (prepared, key) ← prepare store.arena views qv qe parent post child
  let charged ← inventory (store.tables prepared) resources.preparationWork resources.usizeMax
  let allocated := allocate charged {resources.toResources with contextCount := prepared.contexts.length} key
  match allocated.2 with
  | .error failure => some (allocated.1, .error failure)
  | .ok id => some (allocated.1, .ok (receipt parent key child derived id))

theorem admission_success_refines {store after : Store} (history : I.NativeHistory store.native)
    {resources : Funding} {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : P.Key} {post : Nat} {derived : Bool} {child : P.Child} {result : P.Receipt}
    (computed : admit store resources views qv qe parent post derived child = some (after, .ok result)) :
    NativeValuePorts.admit store.arena views qv qe parent post derived child = some (after.arena, result) ∧
    I.NativeHistory after.native ∧ after.native.store.readback result.relation = some result.child ∧
    NativeValuePorts.AdmissionResult after.arena views qv qe parent post derived child result := by
  unfold admit at computed
  obtain ⟨⟨prepared, key⟩, preparation, more⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨charged, chargedAt, more⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨sameArena, chargedHistory, _⟩ := inventory_exact (store := store.tables prepared) history chargedAt
  have actualArena : charged.arena = prepared := sameArena.trans (prepared_physical_tables preparation)
  cases allocated : allocate charged {resources.toResources with contextCount := prepared.contexts.length} key with
  | mk actual outcome =>
      cases outcome with
      | error failure => simp only [allocated] at more; cases more
      | ok id =>
          simp only [allocated] at more
          cases more
          have facts := allocation_exact chargedHistory allocated
          have relation := facts.2.2
          rw [actualArena] at relation
          have pure := prepared_admission derived preparation facts.1
          rw [relation] at pure
          have reachable := allocation_history charged
            {resources.toResources with contextCount := prepared.contexts.length} key chargedHistory
          refine ⟨pure, ?_, facts.2.1, (NativeValuePorts.admit_constructs pure).2⟩
          simpa only [allocated] using reachable

theorem admission_attempt_keeps_history {store after : Store} (history : I.NativeHistory store.native)
    {resources : Funding} {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : P.Key} {post : Nat} {derived : Bool} {child : P.Child}
    {outcome : Except I.Failure P.Receipt}
    (computed : admit store resources views qv qe parent post derived child = some (after, outcome)) :
    I.NativeHistory after.native := by
  unfold admit at computed
  obtain ⟨⟨prepared, key⟩, _, more⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨charged, chargedAt, more⟩ := Option.bind_eq_some_iff.mp more
  have chargedHistory := (inventory_exact (store := store.tables prepared) history chargedAt).2.1
  have reachable := allocation_history charged
    {resources.toResources with contextCount := prepared.contexts.length} key chargedHistory
  cases allocated : allocate charged {resources.toResources with contextCount := prepared.contexts.length} key with
  | mk actual result =>
      cases result <;> simp only [allocated] at more <;> cases more <;>
        simpa only [allocated] using reachable

/-- A single physical relation vector supplies the cursor. The remaining
cursor/drain fields retain their original meaning and arbitrary old queue. -/
structure State where
  store : Store
  done : List P.Child := []
  todo : List P.Child
  pending : Option P.Receipt := none
  records : List NativeValuePorts.Work := []
  queue : List NativeValuePorts.NativeWork := []
  control : D.Control
  tasks : List NativeValuePorts.Pair := []
  receipts : List D.Issuance := []

def State.decoded (state : State) : D.State :=
  ⟨⟨state.store.arena, state.done, state.todo, state.pending, state.records, state.queue⟩,
    state.control, state.tasks, state.receipts⟩

def origin (store : Store) (children : List P.Child) (control : D.Control)
    (tasks : List NativeValuePorts.Pair) : D.Origin :=
  ⟨store.arena, children, control, tasks⟩

def start (store : Store) (children : List P.Child) (control : D.Control)
    (tasks : List NativeValuePorts.Pair) : State :=
  {store := store, todo := children.reverse, control := control, tasks := tasks}

theorem start_decoded (store : Store) (children : List P.Child) (control : D.Control)
    (tasks : List NativeValuePorts.Pair) :
    (start store children control tasks).decoded = NativeValueDrain.start (origin store children control tasks) := rfl

def State.admitted (state : State) (after : Store) (receipt : P.Receipt) : State :=
  {state with store := after, pending := some receipt}

def State.enqueued (state : State) (child : P.Child) (rest : List P.Child)
    (receipt : P.Receipt) : State :=
  let named := NativeValuePorts.intern state.tasks child.task
  let occurrence := NativeDrainOwnership.work state.control named.2 receipt.relation none
  {state with
    done := state.done ++ [child]
    todo := rest
    pending := none
    records := state.records ++ [⟨child, receipt⟩]
    queue := (NativeValuePorts.Work.native ⟨child, receipt⟩) :: state.queue
    control := NativeDrainOwnership.pushWork state.control occurrence true
    tasks := named.1
    receipts := state.receipts ++ [⟨⟨child, receipt⟩, occurrence⟩]}

theorem admitted_decoded (state : State) (after : Store) (receipt : P.Receipt) :
    (state.admitted after receipt).decoded = state.decoded.admitted after.arena receipt := rfl

theorem enqueued_decoded (state : State) (child : P.Child) (rest : List P.Child)
    (receipt : P.Receipt) :
    (state.enqueued child rest receipt).decoded = state.decoded.enqueued child rest receipt := rfl

/-- Computed relation allocation followed by the already accepted two-stage
cursor/enqueue projection. This does not skip the separate native dependency
publication and sampling proof obligation in a whole execution extraction. -/
def drive (resources : Nat → Funding) (views : Nat → Option (Option Nat))
    (qv qe : Nat → Nat) (parent : P.Key) (post : Nat) (derived : Bool) :
    Nat → State → Option State
  | 0, state => if state.todo = [] then some state else none
  | fuel + 1, state =>
      match state.todo with
      | [] => some state
      | child :: rest =>
          match state.pending with
          | none => do
              let (after, outcome) ← admit state.store (resources state.done.length)
                views qv qe parent post derived child
              match outcome with
              | .error _ => none
              | .ok receipt => drive resources views qv qe parent post derived fuel (state.admitted after receipt)
          | some receipt => drive resources views qv qe parent post derived fuel
              (state.enqueued child rest receipt)

theorem drive_refines_emit {resources : Nat → Funding}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : P.Key} {post : Nat} {derived : Bool} {fuel : Nat} {first last : State}
    (history : I.NativeHistory first.store.native)
    (computed : drive resources views qv qe parent post derived fuel first = some last) :
    I.NativeHistory last.store.native ∧
    NativeValueDrain.emit views qv qe parent post derived fuel first.decoded = some last.decoded := by
  induction fuel generalizing first last with
  | zero =>
      unfold drive at computed
      split at computed
      · rename_i finished
        cases computed
        exact ⟨history, by simp [NativeValueDrain.emit, State.decoded, finished]⟩
      · cases computed
  | succ fuel ih =>
      cases next : first.todo with
      | nil =>
          simp only [drive, next] at computed
          cases computed
          exact ⟨history, by simp [NativeValueDrain.emit, State.decoded, next]⟩
      | cons child rest =>
          cases pending : first.pending with
          | none =>
              simp only [drive, next, pending] at computed
              obtain ⟨⟨after, outcome⟩, admitted, more⟩ := Option.bind_eq_some_iff.mp computed
              cases outcome with
              | error failure => cases more
              | ok receipt =>
                  obtain ⟨pure, reachable, _⟩ := admission_success_refines history admitted
                  obtain ⟨lastHistory, exact⟩ := ih (first := first.admitted after receipt) reachable more
                  refine ⟨lastHistory, ?_⟩
                  rw [admitted_decoded] at exact
                  have next' : first.decoded.cursor.todo = child :: rest := next
                  have pending' : first.decoded.cursor.pending = none := pending
                  simp only [NativeValueDrain.emit, next', pending']
                  change (NativeValuePorts.admit first.store.arena views qv qe parent post derived child).bind
                    (fun result => NativeValueDrain.emit views qv qe parent post derived fuel
                      (first.decoded.admitted result.1 result.2)) = some last.decoded
                  rw [pure]
                  exact exact
          | some receipt =>
              simp only [drive, next, pending] at computed
              obtain ⟨lastHistory, exact⟩ := ih (first := first.enqueued child rest receipt) history computed
              refine ⟨lastHistory, ?_⟩
              rw [enqueued_decoded] at exact
              have next' : first.decoded.cursor.todo = child :: rest := next
              have pending' : first.decoded.cursor.pending = some receipt := pending
              simpa only [NativeValueDrain.emit, next', pending'] using exact

theorem registered_is_physical_readback {store : Store}
    (history : I.NativeHistory store.native) {id : Nat} {key : P.Key}
    (registered : store.arena.relations[id]? = some key) :
    store.native.store.readback id = some key := by
  change (store.native.store.relations.map NativeRelationInterner.Entry.origin)[id]? = some key at registered
  rw [List.getElem?_map] at registered
  obtain ⟨entry, found, same⟩ := Option.map_eq_some_iff.mp registered
  subst key
  exact (NativeRelationInterner.history_stored_key_decodes
    (NativeRelationInterner.native_history_refinement history).2 found).2

/-- The physical successful calls construct the exact middle control history;
every resulting receipt also decodes from its stored physical RawKey/FlowId. -/
theorem physical_children_pipeline
    {resources : Nat → Funding} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : P.Key} {post : Nat} {derived : Bool}
    {store : Store} {children : List P.Child} {control prepared : D.Control}
    {tasks : List NativeValuePorts.Pair} {preparationFuel fuel : Nat} {emitted : State}
    (history : I.NativeHistory store.native)
    (prior : NativeDrainOwnership.Run NativeDrainOwnership.initial control)
    (present : D.ParentPresent parent (NativeValueDrain.start (origin store children control tasks)))
    (preparation : NativeValueDrain.prepareAll preparationFuel control = some prepared)
    (computed : drive resources views qv qe parent post derived fuel
      (start store children prepared tasks) = some emitted) :
    I.NativeHistory emitted.store.native ∧
    NativeDrainOwnership.Run NativeDrainOwnership.initial emitted.control ∧
    ∀ last, NativeDrainOwnership.Run emitted.control last → last.queue = [] → last.frames = [] →
      ∃ jobs : List D.Issuance,
        jobs.map (fun job => job.port.source) = children ∧
        ∀ job ∈ jobs,
          job.matches emitted.tasks ∧
          NativeValuePorts.AdmissionResult emitted.store.arena views qv qe parent post derived
            job.port.source job.port.receipt ∧
          emitted.store.native.store.readback job.port.receipt.relation = some job.port.receipt.child ∧
          ∃ returned ∈ last.returns, job.occurrence ∈ returned.frame.processed ∧
            returned.frame.diagnosed = true ∧ returned.frame.phase = .returnReady ∧
            returned.frame.pending = [] ∧ returned.frame.current = none := by
  have active := NativeValueDrain.preflight_parent_active present preparation
  have before := NativeValueDrain.control_run_trans prior
    (NativeValueDrain.prepare_all_exact preparation).1
  obtain ⟨physical, pure⟩ := drive_refines_emit history computed
  rw [start_decoded] at pure
  have initial := NativeValueDrain.start_invariant views qv qe parent post derived
    (origin store children prepared tasks) active
  obtain ⟨run, _⟩ := NativeValueDrain.emit_constructs_run initial pure
  refine ⟨physical, NativeValueDrain.control_run_trans before (NativeValueDrain.run_control run), ?_⟩
  intro last continuation queue stack
  obtain ⟨jobs, sources, every⟩ := NativeValueDrain.emitted_children_returned
    before active pure continuation queue stack
  refine ⟨jobs, sources, ?_⟩
  intro job member
  obtain ⟨matched, checked, returned⟩ := every job member
  exact ⟨matched, checked, registered_is_physical_readback physical checked.registered, returned⟩

/-- The same actual Context/Value branch computes the child vector. Other
native branches retain their existing distinct execution owners; None here
does not redefine which source programs or native runs are supported. -/
def executeChildrenAfterContext
    (contexts : NativeContextExpansion.Tables) (contextFuel : Nat)
    (tables : NativeValueStructure.Tables) (routing : NativeValueStructure.Routing)
    (request : NativeValueStructure.Request) (resources : Nat → Funding)
    (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat) (post : Nat)
    (derived : Bool) (preparationFuel fuel : Nat) (store : Store)
    (control : D.Control) (tasks : List NativeValuePorts.Pair) : Option State := do
  let forwarded ← NativeContextExpansion.valueContext contexts contextFuel request
  if routing.candidate then
    match NativeValueStructure.dispatch tables routing forwarded with
    | .body (.children _ items) => do
        let prepared ← NativeValueDrain.prepareAll preparationFuel control
        drive resources views qv qe (NativeValueStructure.Request.key forwarded) post derived fuel
          (start store items prepared tasks)
    | _ => none
  else none

theorem context_execution_inputs
    {contexts : NativeContextExpansion.Tables} {contextFuel : Nat}
    {tables : NativeValueStructure.Tables} {routing : NativeValueStructure.Routing}
    {request : NativeValueStructure.Request} {resources : Nat → Funding}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {preparationFuel fuel : Nat} {store : Store}
    {control : D.Control} {tasks : List NativeValuePorts.Pair} {emitted : State}
    (computed : executeChildrenAfterContext contexts contextFuel tables routing request resources
      views qv qe post derived preparationFuel fuel store control tasks = some emitted) :
    request.transformer = 0 ∧ routing.candidate = true ∧
    ∃ family items prepared,
      NativeValueStructure.dispatch tables routing request = .body (.children family items) ∧
      NativeValueDrain.prepareAll preparationFuel control = some prepared ∧
      drive resources views qv qe request.key post derived fuel (start store items prepared tasks) = some emitted := by
  unfold executeChildrenAfterContext at computed
  obtain ⟨forwarded, checked, rest⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨same, identity⟩ := NativeContextExpansion.value_context_exact checked
  subst forwarded
  split at rest
  next candidate =>
    cases branch : NativeValueStructure.dispatch tables routing request with
    | duplicate | canonical | retained => simp [branch] at rest
    | body result =>
        cases result with
        | shortcut | diagnostic | fallback | unavailable => simp [branch] at rest
        | children family items =>
            simp only [branch] at rest
            obtain ⟨prepared, preparation, executed⟩ := Option.bind_eq_some_iff.mp rest
            exact ⟨identity, candidate, family, items, prepared, rfl, preparation, executed⟩
  next => cases rest

/-- The outer computation, not a caller-chosen child list, supplies the
complete physical-relation/port/control history and each final raw ID readback. -/
theorem context_physical_pipeline
    {contexts : NativeContextExpansion.Tables} {contextFuel : Nat}
    {tables : NativeValueStructure.Tables} {routing : NativeValueStructure.Routing}
    {request : NativeValueStructure.Request} {resources : Nat → Funding}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {preparationFuel fuel : Nat} {store : Store}
    {control : D.Control} {tasks : List NativeValuePorts.Pair} {emitted : State}
    (history : I.NativeHistory store.native)
    (prior : NativeDrainOwnership.Run NativeDrainOwnership.initial control)
    (present : D.ParentPresent request.key (NativeValueDrain.start (origin store [] control tasks)))
    (computed : executeChildrenAfterContext contexts contextFuel tables routing request resources
      views qv qe post derived preparationFuel fuel store control tasks = some emitted) :
    request.transformer = 0 ∧ routing.candidate = true ∧
    I.NativeHistory emitted.store.native ∧
    NativeDrainOwnership.Run NativeDrainOwnership.initial emitted.control ∧
    ∃ family items,
      NativeValueStructure.dispatch tables routing request = .body (.children family items) ∧
      ∀ last, NativeDrainOwnership.Run emitted.control last → last.queue = [] → last.frames = [] →
        ∃ jobs : List D.Issuance,
          jobs.map (fun job => job.port.source) = items ∧
          ∀ job ∈ jobs,
            job.matches emitted.tasks ∧
            NativeValuePorts.AdmissionResult emitted.store.arena views qv qe request.key post derived
              job.port.source job.port.receipt ∧
            emitted.store.native.store.readback job.port.receipt.relation = some job.port.receipt.child ∧
            ∃ returned ∈ last.returns, job.occurrence ∈ returned.frame.processed ∧
              returned.frame.diagnosed = true ∧ returned.frame.phase = .returnReady ∧
              returned.frame.pending = [] ∧ returned.frame.current = none := by
  obtain ⟨identity, candidate, family, items, prepared, branch, preparation, executed⟩ :=
    context_execution_inputs computed
  have actualParent : D.ParentPresent request.key
      (NativeValueDrain.start (origin store items control tasks)) := present
  obtain ⟨physical, run, returned⟩ := physical_children_pipeline history prior actualParent preparation executed
  exact ⟨identity, candidate, physical, run, family, items, branch, returned⟩

namespace Witness

def demand : NativeContextExpansion.ScopedDemand := ⟨5, 6, 7, 8, 9⟩
def parent : P.Key :=
  ⟨.value .intPositive .intNegative, 0, some 11, ⟨0, some demand⟩⟩
def child : P.Child := ⟨.tuple 0, .value .intPositive .intNegative⟩
def initial : Store := ⟨{}, [], []⟩
def views : Nat → Option (Option Nat) := fun _ => none
def unavailable : Funding := {relationMap := false}
def partialAttempt := admit initial unavailable views id id parent 0 true child

theorem failure_retains_flow_not_receipt :
    (partialAttempt.map fun result => (result.1.native.store.flows.length,
      result.1.native.store.relations.length, result.1.native.store.workUsed,
      match result.2 with | .ok _ => true | .error _ => false)) = some (1, 0, 1, false) := by decide

def failedNative : I.Native := (({} : I.Native).call unavailable.toResources parent).1
def retryStore : Store := ⟨failedNative, [], []⟩
def retryResources : Funding := {enabled := false, flowVector := false, flowMap := false}
def retry := admit retryStore retryResources views id id parent 0 true child

theorem retry_reuses_retained_flow :
    (retry.map fun result => (result.1.native.store.flows.length,
      result.1.native.store.relations.length, result.1.native.store.workUsed,
      match result.2 with | .ok receipt => some (receipt.relation, receipt.child) | .error _ => none)) =
      some (1, 1, 1, some (0, parent)) := by decide

theorem failed_history : I.NativeHistory failedNative :=
  .commit .initial (.call (.nil _) unavailable.toResources parent)

/-- A nonzero preparatory charge is retained even when the subsequent
relation map reservation fails. Its measured amount is an input, not guessed
from a logical transformer record or from a successful body certificate. -/
theorem preparation_work_survives_relation_failure :
    ((admit initial {unavailable with preparationWork := 7} views id id parent 0 true child).map
      fun result => (result.1.native.store.workUsed, result.1.native.store.flows.length,
        result.1.native.store.relations.length,
        match result.2 with | .ok _ => true | .error _ => false)) = some (8, 1, 0, false) := by decide

theorem actual_context_frontier_checked :
    ((admit initial {contextCount := 99} views id id parent 1 true child).map
      fun result => result.2) = some (.error .contextAssertion) := rfl

def functionNative : I.Native :=
  (({} : I.Native).call {contextCount := 1} NativeValuePorts.Witness.parent).1
def functionStore : Store := ⟨functionNative, [.without 0], []⟩
def functionFunding (step : Nat) : Funding :=
  {preparationWork := if step = 1 then 8 else if step = 2 then 2 else 0}
def functionStart : State := start functionStore NativeValuePorts.Witness.children
  NativeValueDrain.Witness.taken [NativeValuePorts.Witness.parent.pair]
def functionExecution := drive functionFunding NativeValuePorts.Witness.views id id
  NativeValuePorts.Witness.parent 1 true 8 functionStart

theorem four_physical_ports :
    (functionExecution.map fun state => (state.receipts.length,
      state.receipts.map (fun record => record.occurrence.serial),
      state.receipts.map (fun record => record.port.receipt.relation),
      state.store.native.store.workUsed, state.store.native.store.relations.length)) =
      some (4, [1, 2, 3, 4], [1, 2, 3, 4], 13, 5) := by decide

theorem function_native_history : I.NativeHistory functionNative :=
  .commit .initial (.call (.nil _) {contextCount := 1} NativeValuePorts.Witness.parent)

theorem function_parent_present : D.ParentPresent NativeValuePorts.Witness.parent
    (NativeValueDrain.start (origin functionStore NativeValuePorts.Witness.children
      NativeValueDrain.Witness.taken [NativeValuePorts.Witness.parent.pair])) := by
  exact ⟨NativeValueDrain.Witness.activeFrame, [], NativeValueDrain.Witness.parentWork, 0,
    rfl, rfl, rfl, rfl, rfl⟩

theorem four_ports_have_one_control_history :
    ∃ emitted, functionExecution = some emitted ∧ I.NativeHistory emitted.store.native ∧
      NativeDrainOwnership.Run NativeDrainOwnership.initial emitted.control := by
  have succeeds : functionExecution.isSome = true := by decide
  obtain ⟨emitted, computed⟩ := Option.isSome_iff_exists.mp succeeds
  have complete := physical_children_pipeline function_native_history
    NativeValueDrain.Witness.actual_parent_prefix function_parent_present
    (show NativeValueDrain.prepareAll 0 NativeValueDrain.Witness.taken =
      some NativeValueDrain.Witness.taken from rfl) computed
  exact ⟨emitted, computed, complete.1, complete.2.1⟩

end Witness

end YulangClosure.NativeValueRelationExecution
