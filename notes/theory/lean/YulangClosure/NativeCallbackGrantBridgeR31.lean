import Std

/-!
R24 schema R1: 686c96c8f8b5417b075a18954f773ad4071996e51e809d65040a87441c342c3c.
This is a conditional, branching record projection, not source typing or a
native simulation theorem. Source baseline: 9a74a70a32ebda716a00c7203d8e606343cf442a.

Authority: annotation-effect-hygiene-integration §§1.1,1.2,3,4. Parent:
intrusion-source-preservation-proof §§1,3,5, corrected by birth-level-SCC §§2–6.
The original all-source quantifiers, shared strategy, Call/effect clauses,
principality and termination remain open. No existing source definition is changed.

Owner map: T1 receiving.rs:70–101; T2 machine.rs:1595–1607; T3 receiving.rs:307–342;
T4 machine.rs:924–965; T5 receiving.rs:345–423; T6 machine.rs:1346–1353;
T7 machine.rs:2852–2871; T8/T9/T11/T13 machine.rs:2354–2487;
T10 ordinary owner return; request unwind machine.rs:2529–2574;
T14 machine.rs:2605–2615. Abandoned global materialization cells are not effect
write contributions. Normal return, request unwind and shallow discard are
separate constructors. T1–T14 are not a required linear trace.

The finite projection keeps permission, actual request, committed consumer and
lifetime records separate. The checked joins below concern supplied typed records;
there is no claim that Rust has constructed these records. Full RootComp image
reachability, general typed-port Flow/Path, symbolic rows, wildcard/release,
continuation replay and the full source language remain outside this projection.
-/
namespace YulangClosure.CallbackHygieneCorrespondence

inductive Kind where
  | declaration | definition | binding | formal | invocation | entry | use | view | receipt | event | payload | arm | handler | cell
  deriving DecidableEq, Repr

structure Id (kind : Kind) where
  ordinal : Nat
  deriving DecidableEq, Repr

structure Site where
  root : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  deriving DecidableEq, Repr

structure Operation where
  declaration : Id .declaration
  family : Nat
  deriving DecidableEq, Repr

inductive Port where
  | callbackResult | rootComp
  deriving DecidableEq, Repr

/-- Static source annotation: it has no runtime invocation identity. -/
structure Annotation where
  definition : Option (Id .definition)
  binding : Option (Id .binding)
  lambdaSite : Site
  formal : Id .formal
  port : Port
  families : List Nat
  deriving DecidableEq, Repr

/-- The invocation-instantiated permission is distinct from actual contribution. -/
structure Permission where
  definition : Option (Id .definition)
  binding : Option (Id .binding)
  lambdaSite : Site
  formal : Id .formal
  owner : Id .invocation
  port : Port
  families : List Nat
  deriving DecidableEq, Repr

def Permission.annotation (p : Permission) : Annotation :=
  ⟨p.definition, p.binding, p.lambdaSite, p.formal, p.port, p.families⟩

structure Invocation where
  handle : Id .invocation
  callSite : Site
  providerSite : Site
  deriving DecidableEq, Repr

structure Receipt where
  handle : Id .receipt
  owner : Id .invocation
  view : Id .view
  site : Site
  formal : Option (Id .formal)
  deriving DecidableEq, Repr

structure Entry where
  handle : Id .entry
  permission : Permission
  incomingView : Id .view
  view : Id .view
  value : Id .payload
  formalReceipt : Receipt
  deriving DecidableEq, Repr

structure NameRead where
  entry : Id .entry
  formal : Id .formal
  site : Site
  receipt : Receipt
  deriving DecidableEq, Repr

structure CallbackUse where
  handle : Id .use
  entry : Id .entry
  owner : Id .invocation
  sourceView : Id .view
  formalReceipt : Id .receipt
  nameReceipt : Id .receipt
  callee : Site
  applySite : Site
  resultView : Id .view
  resultReceipt : Receipt
  deriving DecidableEq, Repr

/-- Exact record coordinates; this does not reconstruct a source derivation. -/
def UseReady (e : Entry) (n : NameRead) (u : CallbackUse) : Prop :=
  e.permission.port = .callbackResult ∧
  e.formalReceipt.owner = e.permission.owner ∧
  e.formalReceipt.view = e.view ∧
  e.formalReceipt.site = e.permission.lambdaSite ∧
  e.formalReceipt.formal = some e.permission.formal ∧
  n.entry = e.handle ∧ n.formal = e.permission.formal ∧
  n.receipt.owner = e.permission.owner ∧ n.receipt.view = e.view ∧
  n.receipt.site = n.site ∧ n.receipt.formal = none ∧
  u.entry = e.handle ∧ u.owner = e.permission.owner ∧
  u.sourceView = e.view ∧ u.formalReceipt = e.formalReceipt.handle ∧
  u.nameReceipt = n.receipt.handle ∧ u.callee = n.site ∧
  u.resultReceipt.owner = u.owner ∧ u.resultReceipt.view = u.resultView ∧
  u.resultReceipt.site = u.applySite ∧ u.resultReceipt.formal = none

instance (e : Entry) (n : NameRead) (u : CallbackUse) : Decidable (UseReady e n u) :=
  by unfold UseReady; infer_instance

def checkedUse (e : Entry) (n : NameRead) (u : CallbackUse) : Option CallbackUse :=
  if UseReady e n u then some u else none

structure Execution where
  useHandle : Id .use
  view : Id .view
  receipt : Id .receipt
  occurrence : Nat
  deriving DecidableEq, Repr

inductive Origin where
  | callback (execution : Execution)
  | computation (view : Id .view) (receipt : Id .receipt)
  deriving DecidableEq, Repr

structure Request where
  event : Id .event
  operation : Operation
  payload : Id .payload
  source : Site
  owner : Id .invocation
  lineage : Id .invocation
  origin : Origin
  deriving DecidableEq, Repr

structure Arm where
  handle : Id .arm
  site : Site
  operation : Operation
  deriving DecidableEq, Repr

structure InstalledCatch where
  handle : Id .handler
  site : Site
  owner : Id .invocation
  arms : List Arm
  deriving DecidableEq, Repr

/-- Exact Catch/arm identity is supplied independently of result equality. -/
structure Consumer where
  handler : Id .handler
  catchSite : Site
  arm : Id .arm
  armSite : Site
  owner : Id .invocation
  operation : Operation
  event : Id .event
  payload : Id .payload
  result : Int
  deriving DecidableEq, Repr

structure Selection where
  request : Request
  consumer : Consumer
  permission : Permission
  deriving DecidableEq, Repr

inductive Lifetime where
  | normalReturn (owner : Id .invocation)
  | requestUnwind (owner : Id .invocation)
  | shallowDiscard (suffixCells : List (Id .cell))
  deriving DecidableEq, Repr

structure State where
  annotations : List Annotation := []
  permissions : List Permission := []
  installed : List InstalledCatch := []
  active : List (Id .invocation) := []
  invocations : List Invocation := []
  entries : List Entry := []
  names : List NameRead := []
  uses : List CallbackUse := []
  executions : List Execution := []
  executing : List Execution := []
  emitted : List Request := []
  pending : List Request := []
  selections : List Selection := []
  initializing : List (Id .cell) := []
  lifetime : List Lifetime := []
  nextEvent : Nat := 0
  nextInvocation : Nat := 0
  deriving DecidableEq, Repr

/-- The callback projection checks entry, formal, Name, use and historical
execution together. The RootComp branch records only its concrete port: native
image/receipt reachability is deliberately still an explicit omitted bridge. -/
def PortReady (s : State) (r : Request) (p : Permission) : Prop :=
  (∃ e ∈ s.entries, ∃ n ∈ s.names, ∃ u ∈ s.uses, ∃ x ∈ s.executions,
    e.permission = p ∧ checkedUse e n u = some u ∧
    x.useHandle = u.handle ∧ x.view = u.resultView ∧
    x.receipt = u.resultReceipt.handle ∧ r.origin = .callback x) ∨
  (p.port = .rootComp ∧ match r.origin with
    | .computation _ _ => True
    | .callback _ => False)

instance (s : State) (r : Request) (p : Permission) : Decidable (PortReady s r p) := by
  unfold PortReady
  cases r.origin <;> infer_instance

/-- Lower-level consumer guard only. Actual native Grant/image authentication
is an additional source-correspondence duty, not inferred from these joins. -/
def CatchReady (s : State) (r : Request) (c : Consumer) (p : Permission) : Prop :=
  r ∈ s.pending ∧ p ∈ s.permissions ∧ c.owner ∈ s.active ∧
  c.owner = p.owner ∧ r.operation.family ∈ p.families ∧ PortReady s r p ∧
  c.operation = r.operation ∧ c.event = r.event ∧ c.payload = r.payload ∧
  ∃ h ∈ s.installed, c.handler = h.handle ∧ c.catchSite = h.site ∧ c.owner = h.owner ∧
    ∃ a ∈ h.arms, c.arm = a.handle ∧ c.armSite = a.site ∧ c.operation = a.operation

instance (s : State) (r : Request) (c : Consumer) (p : Permission) :
    Decidable (CatchReady s r c p) := by unfold CatchReady; infer_instance

def checkedCatch (s : State) (r : Request) (c : Consumer) (p : Permission) :
    Option Selection :=
  if CatchReady s r c p then some ⟨r, c, p⟩ else none

/-- Request creation assigns the event ordinal; permission creation never calls this. -/
def minted (s : State) (r : Request) : Request := { r with event := ⟨s.nextEvent⟩ }

def emit (s : State) (r : Request) : State :=
  { s with emitted := minted s r :: s.emitted, pending := minted s r :: s.pending, nextEvent := s.nextEvent + 1 }

/-- Consume the selected event, retaining every different actual event. -/
def commit (s : State) (x : Selection) : State :=
  { s with pending := s.pending.filter (fun r => decide (r.event ≠ x.request.event)), selections := x :: s.selections, installed := s.installed.filter (fun h => decide (h.handle ≠ x.consumer.handler)) }

/-- Constructor projection with independent branches. In particular the companion
has no callback-use premise, and discard does not stand in for ordinary return. -/
inductive Step : State → State → Prop where
  | annotation (s : State) (a : Annotation) :
      Step s {s with annotations := a :: s.annotations}
  | invocation (s : State) (callSite providerSite : Site) :
      Step s {s with active := ⟨s.nextInvocation⟩ :: s.active, invocations := ⟨⟨s.nextInvocation⟩, callSite, providerSite⟩ :: s.invocations, nextInvocation := s.nextInvocation + 1}
  | installCatch (s : State) (h : InstalledCatch) (live : h.owner ∈ s.active) :
      Step s {s with installed := h :: s.installed}
  | entry (s : State) (e : Entry)
      (annotation : e.permission.annotation ∈ s.annotations)
      (live : e.permission.owner ∈ s.active) (freshEntry : e.handle.ordinal = s.entries.length) :
      Step s {s with entries := e :: s.entries, permissions := e.permission :: s.permissions}
  | rootEntry (s : State) (p : Permission) (annotation : p.annotation ∈ s.annotations)
      (live : p.owner ∈ s.active) (port : p.port = .rootComp) :
      Step s {s with permissions := p :: s.permissions}
  | nameRead (s : State) (e : Entry) (n : NameRead)
      (entry : e ∈ s.entries) (entryId : n.entry = e.handle)
      (owner : n.receipt.owner = e.permission.owner) :
      Step s {s with names := n :: s.names}
  | callbackUse (s : State) (e : Entry) (n : NameRead) (u : CallbackUse)
      (entry : e ∈ s.entries) (name : n ∈ s.names)
      (freshUse : u.handle.ordinal = s.uses.length)
      (checked : checkedUse e n u = some u) :
      Step s {s with uses := u :: s.uses}
  | resultConsumer (s : State) (u : CallbackUse) (useRecord : u ∈ s.uses) :
      Step s {s with executions := ⟨u.handle, u.resultView, u.resultReceipt.handle, s.executions.length⟩ :: s.executions, executing := ⟨u.handle, u.resultView, u.resultReceipt.handle, s.executions.length⟩ :: s.executing}
  | closeExecution (s : State) (x : Execution) (rest : List Execution)
      (top : s.executing = x :: rest) : Step s {s with executing := rest}
  | callbackRequest (s : State) (r : Request) (x : Execution)
      (execution : x ∈ s.executing) (origin : r.origin = .callback x) :
      Step s (emit s r)
  | computationRequest (s : State) (r : Request) (view : Id .view) (receipt : Id .receipt)
      (origin : r.origin = .computation view receipt) : Step s (emit s r)
  | candidate (s : State) (r : Request) (c : Consumer) (p : Permission) (x : Selection)
      (checked : checkedCatch s r c p = some x) : Step s s
  | catchCommit (s : State) (r : Request) (c : Consumer) (p : Permission) (x : Selection)
      (checked : checkedCatch s r c p = some x) : Step s (commit s x)
  | normalReturn (s : State) (owner : Id .invocation) (live : owner ∈ s.active) :
      Step s {s with active := s.active.filter (fun current => decide (current ≠ owner)), lifetime := .normalReturn owner :: s.lifetime}
  | companionInnerCatch (s : State) (r : Request) (c : Consumer) (p : Permission)
      (x : Selection) (checked : checkedCatch s r c p = some x) : Step s (commit s x)
  | companionWrite (s : State) (inner : Selection) (r : Request)
      (innerSelected : inner ∈ s.selections)
      (lineage : r.lineage = inner.request.lineage)
      (independentOperation : r.operation ≠ inner.request.operation)
      (view : Id .view) (receipt : Id .receipt)
      (origin : r.origin = .computation view receipt) : Step s (emit s r)
  | companionOuterReceive (s : State) (r : Request) (c : Consumer) (p : Permission)
      (x : Selection) (checked : checkedCatch s r c p = some x) : Step s (commit s x)
  | requestUnwind (s : State) (owner : Id .invocation) (live : owner ∈ s.active) :
      Step s {s with active := s.active.filter (fun current => decide (current ≠ owner)), lifetime := .requestUnwind owner :: s.lifetime}
  | shallowDiscard (s : State) (suffixCells : List (Id .cell)) :
      Step s {s with initializing := s.initializing.filter (fun cell => decide (cell ∉ suffixCells)), lifetime := .shallowDiscard suffixCells :: s.lifetime}

/-- Actual-event provenance and exact consumer coordinates, without assuming
that any annotation emits an event or that any desired residual already holds. -/
def Conserved (s : State) : Prop :=
  (∀ r ∈ s.pending, r ∈ s.emitted) ∧
  (∀ x ∈ s.selections, x.request ∈ s.emitted ∧
    x.consumer.operation = x.request.operation ∧
    x.consumer.event = x.request.event ∧ x.consumer.payload = x.request.payload ∧
    x.consumer.owner = x.permission.owner ∧
    x.request.operation.family ∈ x.permission.families)

theorem checked_use_inversion {e : Entry} {n : NameRead} {u out : CallbackUse}
    (checked : checkedUse e n u = some out) : out = u ∧ UseReady e n u := by
  unfold checkedUse at checked
  split at checked
  next ready => exact ⟨(Option.some.inj checked).symm, ready⟩
  next _ => cases checked

theorem checked_catch_inversion {s : State} {r : Request} {c : Consumer}
    {p : Permission} {x : Selection} (checked : checkedCatch s r c p = some x) :
    x = ⟨r, c, p⟩ ∧ CatchReady s r c p := by
  unfold checkedCatch at checked
  split at checked
  next ready => exact ⟨(Option.some.inj checked).symm, ready⟩
  next _ => cases checked

/-- Invert the installed delimiter and its exact arm; result equality is not a key. -/
theorem checked_catch_installed_arm {s : State} {r : Request} {c : Consumer}
    {p : Permission} {x : Selection} (checked : checkedCatch s r c p = some x) :
    ∃ h ∈ s.installed, c.handler = h.handle ∧ c.catchSite = h.site ∧ c.owner = h.owner ∧
      ∃ a ∈ h.arms, c.arm = a.handle ∧ c.armSite = a.site ∧ c.operation = a.operation := by
  obtain ⟨_, ready⟩ := checked_catch_inversion checked
  exact ready.2.2.2.2.2.2.2.2.2

theorem checked_catch_port {s : State} {r : Request} {c : Consumer}
    {p : Permission} {x : Selection} (checked : checkedCatch s r c p = some x) :
    PortReady s r p := by
  obtain ⟨_, ready⟩ := checked_catch_inversion checked
  exact ready.2.2.2.2.2.1

/-- No actual request is fabricated by publishing a contravariant permission. -/
theorem permission_preserves_actual (s : State) (a : Annotation) :
    ({s with annotations := a :: s.annotations} : State).emitted = s.emitted ∧
    ({s with annotations := a :: s.annotations} : State).pending = s.pending := ⟨rfl, rfl⟩

theorem emit_conserved {s : State} (inv : Conserved s) (r : Request) :
    Conserved (emit s r) := by
  constructor
  · intro q member
    rcases List.mem_cons.mp member with same | old
    · exact List.mem_cons.mpr (.inl same)
    · exact List.mem_cons.mpr (.inr (inv.1 q old))
  · intro x member
    obtain ⟨actual, operation, event, payload, owner, permission⟩ := inv.2 x member
    exact ⟨List.mem_cons.mpr (.inr actual), operation, event, payload, owner, permission⟩

theorem commit_conserved {s : State} (inv : Conserved s)
    {r : Request} {c : Consumer} {p : Permission} {x : Selection}
    (checked : checkedCatch s r c p = some x) : Conserved (commit s x) := by
  obtain ⟨rfl, ready⟩ := checked_catch_inversion checked
  rcases ready with ⟨pending, _, _, owner, permission, _, operation, event, payload, _⟩
  constructor
  · intro q member
    exact inv.1 q (List.mem_filter.mp member).1
  · intro y member
    rcases List.mem_cons.mp member with same | old
    · subst y
      exact ⟨inv.1 r pending, operation, event, payload, owner, permission⟩
    · exact inv.2 y old

theorem step_conserved {before after : State} (step : Step before after)
    (inv : Conserved before) : Conserved after := by
  cases step with
  | callbackRequest r x execution origin => exact emit_conserved inv r
  | computationRequest r view receipt origin => exact emit_conserved inv r
  | companionWrite inner r selected lineage independent view receipt origin =>
      exact emit_conserved inv r
  | catchCommit r c p x checked => exact commit_conserved inv checked
  | companionInnerCatch r c p x checked => exact commit_conserved inv checked
  | companionOuterReceive r c p x checked => exact commit_conserved inv checked
  | _ => exact inv

inductive History : State → State → Prop where
  | refl (s : State) : History s s
  | next {initial before after : State} :
      History initial before → Step before after → History initial after

theorem history_conserved {initial final : State} (history : History initial final)
    (inv : Conserved initial) : Conserved final := by
  induction history with
  | refl => exact inv
  | next history step ih => exact step_conserved step ih

theorem empty_conserved : Conserved ({} : State) := by
  constructor <;> intro x member <;> cases member

/-- The request owner, rather than a caller label, allocates increasing events. -/
def EventsBefore (s : State) : Prop :=
  ∀ r ∈ s.emitted, r.event.ordinal < s.nextEvent

theorem emit_events_before {s : State} (inv : EventsBefore s) (r : Request) :
    EventsBefore (emit s r) := by
  intro q member
  rcases List.mem_cons.mp member with same | old
  · subst q
    exact Nat.lt_succ_self s.nextEvent
  · exact Nat.lt_trans (inv q old) (Nat.lt_succ_self s.nextEvent)

theorem step_events_before {before after : State} (step : Step before after)
    (inv : EventsBefore before) : EventsBefore after := by
  cases step with
  | callbackRequest r x execution origin => exact emit_events_before inv r
  | computationRequest r view receipt origin => exact emit_events_before inv r
  | companionWrite inner r selected lineage independent view receipt origin =>
      exact emit_events_before inv r
  | _ => exact inv

theorem generated_events_before {final : State} (history : History {} final) :
    EventsBefore final := by
  have initial : EventsBefore ({} : State) := by
    intro r member
    cases member
  induction history with
  | refl => exact initial
  | next history step ih => exact step_events_before step ih

/-- Every selected event in a generated history was actually emitted. This
is a projection theorem, not the original all-source effect-hygiene theorem. -/
theorem generated_selection_actual {final : State} (history : History {} final)
    {x : Selection} (selected : x ∈ final.selections) :
    x.request ∈ final.emitted ∧ x.consumer.operation = x.request.operation ∧
    x.consumer.event = x.request.event ∧ x.consumer.payload = x.request.payload ∧
    x.consumer.owner = x.permission.owner ∧
    x.request.operation.family ∈ x.permission.families :=
  (history_conserved history empty_conserved).2 x selected

/-- Permission alone cannot make a Catch commit at an empty inflow. -/
theorem empty_inflow_rejected (s : State) (r : Request) (c : Consumer)
    (p : Permission) (empty : s.pending = []) : checkedCatch s r c p = none := by
  simp [checkedCatch, CatchReady, empty]

/-- T12's later event cannot be the already consumed inner signal's event.
This discharges the distinct-event condition from generated history, not from
matching family text, identical payloads, or equal result values. -/
theorem companion_event_fresh {s : State} (history : History {} s)
    {inner : Selection} (selected : inner ∈ s.selections) (r : Request) :
    (minted s r).event ≠ inner.request.event := by
  have prior := (generated_selection_actual history selected).1
  have bounded := generated_events_before history inner.request prior
  intro equal
  have ord : inner.request.event.ordinal = s.nextEvent :=
    (congrArg (fun event : Id .event => event.ordinal) equal).symm
  exact Nat.ne_of_lt bounded ord

/-- The signal consumer preserves any independently minted write event. The
distinct-event premise must come from authenticated request-owner ordinals. -/
theorem commit_preserves_other_event (s : State) (x : Selection) (write : Request)
    (incoming : write ∈ s.pending) (different : write.event ≠ x.request.event) :
    write ∈ (commit s x).pending := by
  exact List.mem_filter.mpr ⟨incoming, by simpa using different⟩

theorem commit_removes_selected_event (s : State) (x : Selection) :
    ∀ r ∈ (commit s x).pending, r.event ≠ x.request.event := by
  intro r member
  have kept := (List.mem_filter.mp member).2
  simpa using kept

/-- T12 creates an actual companion contribution with the owner-minted event;
T11 does not invent it from an annotation. -/
theorem companion_emit_actual (s : State) (r : Request) :
    minted s r ∈ (emit s r).emitted ∧ minted s r ∈ (emit s r).pending ∧
    (minted s r).operation = r.operation ∧ (minted s r).payload = r.payload ∧
    (minted s r).lineage = r.lineage := by
  exact ⟨List.mem_cons_self, List.mem_cons_self, rfl, rfl, rfl⟩

/-- Shallow discard concerns pending cache materialization, never an emitted
effect contribution; request-unwind retirement has its own prior transition. -/
theorem shallow_discard_preserves_contributions (s : State) (cells : List (Id .cell)) :
    ({s with initializing := s.initializing.filter (fun cell => decide (cell ∉ cells)), lifetime := .shallowDiscard cells :: s.lifetime} : State).pending = s.pending ∧
    ({s with initializing := s.initializing.filter (fun cell => decide (cell ∉ cells)), lifetime := .shallowDiscard cells :: s.lifetime} : State).emitted = s.emitted ∧
    ({s with initializing := s.initializing.filter (fun cell => decide (cell ∉ cells)), lifetime := .shallowDiscard cells :: s.lifetime} : State).active = s.active := ⟨rfl, rfl, rfl⟩

theorem normal_return_deactivates (s : State) (owner : Id .invocation) :
    owner ∉ ({s with active := s.active.filter (fun current => decide (current ≠ owner)), lifetime := .normalReturn owner :: s.lifetime} : State).active := by
  intro member
  have different : owner ≠ owner := of_decide_eq_true (List.mem_filter.mp member).2
  exact different rfl

/-- The two lifetime events cannot be authenticated by equal arm result values. -/
theorem lifetime_branches_distinct (owner : Id .invocation) (cells : List (Id .cell)) :
    Lifetime.normalReturn owner ≠ Lifetime.shallowDiscard cells := by
  intro equal
  cases equal

/-!
Parent application: `generated_selection_actual` supplies actual-event and
exact consumer-coordinate obligations for a History witness, while
`commit_preserves_other_event` supplies the residual-event clause for a distinct
write event. Neither constructs History from native execution. First remaining
premise: authenticate one projection of the frozen owner-hook records (including
native Grant, full Site/arm keys, ordinals, source use joins and lifetime branches)
to Step/History, then instantiate these theorems on both selected occurrences.
This is owned by the Rust/source correspondence lane and independent reviewer.
The source-derived callback's arm returning 1 and companion outer result 23
require exact authenticated arm-body execution; neither is inferred here.
-/
end YulangClosure.CallbackHygieneCorrespondence

/-!
R31 construction. The exact pinned R26 source above is embedded byte-for-byte.
Below, Module, Parse and Green are abstract identity types. They represent typed
ModuleId equality, parse allocation identity and green allocation identity;
instantiating them from native bytes remains an extraction obligation. No Debug
rendering or source span is an identity encoding. Native operation identity is
its complete effect family plus its own declaration key. The finite table is
supplied for one snapshot and membership is explicit; absent identities have no
claimed decoding law. Duplicate table entries are allowed; first-index encoding
is still injective on members. Table indices are not persistent native IDs.
-/
namespace YulangClosure.NativeCallbackGrantBridgeR31
open CallbackHygieneCorrespondence

structure SourceNodeKey (Parse Green : Type) where
  parseIdentity : Parse
  greenIdentity : Green
  start : Nat
  deriving DecidableEq

structure SourceEffectId (Module Parse Green : Type) where
  moduleIdentity : Module
  declaration : SourceNodeKey Parse Green
  deriving DecidableEq

structure SourceOperationId (Module Parse Green : Type) where
  family : SourceEffectId Module Parse Green
  declaration : SourceNodeKey Parse Green
  deriving DecidableEq

variable {Module Parse Green : Type}
variable [DecidableEq Module] [DecidableEq Parse] [DecidableEq Green]

structure IdentityTable (Module Parse Green : Type) where
  families : List (SourceEffectId Module Parse Green)
  operations : List (SourceOperationId Module Parse Green)

/-- A real lookup law, proved using membership, rather than an assumed inverse. -/
theorem finite_index_round_trip {α : Type} [DecidableEq α]
    (table : List α) (a : α) (member : a ∈ table) :
    table[table.idxOf a]? = some a := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem member)]
  exact congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem member))

theorem finite_index_injective {α : Type} [DecidableEq α]
    (table : List α) {a b : α} (ha : a ∈ table) (hb : b ∈ table)
    (same : table.idxOf a = table.idxOf b) : a = b := by
  have ea := finite_index_round_trip table a ha
  have eb := finite_index_round_trip table b hb
  rw [same] at ea
  exact Option.some.inj (ea.symm.trans eb)

def operationKey (table : IdentityTable Module Parse Green)
    (operation : SourceOperationId Module Parse Green) : Operation :=
  ⟨⟨table.operations.idxOf operation⟩, table.families.idxOf operation.family⟩

def decodeOperation (table : IdentityTable Module Parse Green)
    (key : Operation) : Option (SourceOperationId Module Parse Green) := do
  let operation ← table.operations[key.declaration.ordinal]?
  if table.families[ key.family ]? = some operation.family then some operation else none

theorem operation_round_trip (table : IdentityTable Module Parse Green)
    (operation : SourceOperationId Module Parse Green)
    (opMember : operation ∈ table.operations)
    (familyMember : operation.family ∈ table.families) :
    decodeOperation table (operationKey table operation) = some operation := by
  simp [decodeOperation, operationKey, finite_index_round_trip table.operations operation opMember,
    finite_index_round_trip table.families operation.family familyMember]

theorem operationKey_injective (table : IdentityTable Module Parse Green)
    {a b : SourceOperationId Module Parse Green}
    (ha : a ∈ table.operations) (hb : b ∈ table.operations)
    (same : operationKey table a = operationKey table b) : a = b := by
  apply finite_index_injective table.operations ha hb
  exact congrArg (fun key : Operation => key.declaration.ordinal) same

theorem encoded_family_member (table : IdentityTable Module Parse Green)
    {family : SourceEffectId Module Parse Green}
    {row : List (SourceEffectId Module Parse Green)} (member : family ∈ row) :
    table.families.idxOf family ∈ row.map table.families.idxOf :=
  List.mem_map.mpr ⟨family, member, rfl⟩

theorem encoded_family_member_iff (table : IdentityTable Module Parse Green)
    {family : SourceEffectId Module Parse Green}
    {row : List (SourceEffectId Module Parse Green)}
    (covered : ∀ f ∈ row, f ∈ table.families)
    (familyMember : family ∈ table.families) :
    table.families.idxOf family ∈ row.map table.families.idxOf ↔ family ∈ row := by
  constructor
  · intro member
    obtain ⟨f, inRow, same⟩ := List.mem_map.mp member
    have equal := finite_index_injective table.families (covered f inRow) familyMember same
    exact equal ▸ inRow
  · exact encoded_family_member table

/-- Non-operation coordinates remain separate; the old core operation slot is
replaced, so it cannot supply an operation identity to the projection. -/
structure NativeRequest (Module Parse Green : Type) where
  coordinates : Request
  operation : SourceOperationId Module Parse Green

structure NativeConsumer (Module Parse Green : Type) where
  coordinates : Consumer
  operation : SourceOperationId Module Parse Green

structure NativeArm (Module Parse Green : Type) where
  coordinates : Arm
  operation : SourceOperationId Module Parse Green

def requestKey (t : IdentityTable Module Parse Green)
    (r : NativeRequest Module Parse Green) : Request :=
  {r.coordinates with operation := operationKey t r.operation}

def consumerKey (t : IdentityTable Module Parse Green)
    (c : NativeConsumer Module Parse Green) : Consumer :=
  {c.coordinates with operation := operationKey t c.operation}

def armKey (t : IdentityTable Module Parse Green)
    (a : NativeArm Module Parse Green) : Arm :=
  {a.coordinates with operation := operationKey t a.operation}

/-- All R26 callback joins remain explicit independent coordinate premises.
This is a finite slice, not an authenticated native store or History. -/
def callbackSlice (e : Entry) (n : NameRead) (u : CallbackUse) (x : Execution)
    (r : Request) (p : Permission) (active : List (Id .invocation))
    (installed : InstalledCatch) : State :=
  {entries := [e], names := [n], uses := [u], executions := [x],
   pending := [r], emitted := [r], permissions := [p], active := active,
   installed := [installed]}

/-- Derive the full R26 UseReady conjunction from independently named joins;
no UseReady/PortReady/CatchReady or successful checker is a premise. -/
theorem callback_use_ready (e : Entry) (n : NameRead) (u : CallbackUse)
    (port : e.permission.port = .callbackResult)
    (formalOwner : e.formalReceipt.owner = e.permission.owner)
    (formalView : e.formalReceipt.view = e.view)
    (formalSite : e.formalReceipt.site = e.permission.lambdaSite)
    (formalParameter : e.formalReceipt.formal = some e.permission.formal)
    (nameEntry : n.entry = e.handle) (nameFormal : n.formal = e.permission.formal)
    (nameOwner : n.receipt.owner = e.permission.owner)
    (nameView : n.receipt.view = e.view) (nameSite : n.receipt.site = n.site)
    (nameParameter : n.receipt.formal = none)
    (useEntry : u.entry = e.handle) (useOwner : u.owner = e.permission.owner)
    (useView : u.sourceView = e.view)
    (useFormal : u.formalReceipt = e.formalReceipt.handle)
    (useName : u.nameReceipt = n.receipt.handle) (callee : u.callee = n.site)
    (resultOwner : u.resultReceipt.owner = u.owner)
    (resultView : u.resultReceipt.view = u.resultView)
    (resultSite : u.resultReceipt.site = u.applySite)
    (resultParameter : u.resultReceipt.formal = none) : UseReady e n u :=
  ⟨port, formalOwner, formalView, formalSite, formalParameter, nameEntry,
   nameFormal, nameOwner, nameView, nameSite, nameParameter, useEntry,
   useOwner, useView, useFormal, useName, callee, resultOwner, resultView,
   resultSite, resultParameter⟩

/-- Conditional finite callback/Catch bridge. Full source sites are retained.
The permission row is projected from structural families. Dynamic installation,
exact arm, request origin, and invocation joins are independently supplied.
UseReady remains a local obligation discharged by callback_use_ready above;
this theorem supplies no successful native Grant or source derivation. -/
theorem callback_checked_catch
    (table : IdentityTable Module Parse Green)
    (r : NativeRequest Module Parse Green) (c : NativeConsumer Module Parse Green)
    (a : NativeArm Module Parse Green) (e : Entry) (n : NameRead)
    (u : CallbackUse) (x : Execution) (active : List (Id .invocation))
    (installation : InstalledCatch) (families : List (SourceEffectId Module Parse Green))
    (useJoins : UseReady e n u)
    (handle : x.useHandle = u.handle) (view : x.view = u.resultView)
    (receipt : x.receipt = u.resultReceipt.handle)
    (origin : r.coordinates.origin = .callback x)
    (row : e.permission.families = families.map table.families.idxOf)
    (family : r.operation.family ∈ families)
    (live : c.coordinates.owner ∈ active)
    (owner : c.coordinates.owner = e.permission.owner)
    (operation : c.operation = r.operation)
    (event : c.coordinates.event = r.coordinates.event)
    (payload : c.coordinates.payload = r.coordinates.payload)
    (handler : c.coordinates.handler = installation.handle)
    (catchSite : c.coordinates.catchSite = installation.site)
    (installationOwner : c.coordinates.owner = installation.owner)
    (armMember : armKey table a ∈ installation.arms)
    (arm : c.coordinates.arm = a.coordinates.handle)
    (armSite : c.coordinates.armSite = a.coordinates.site)
    (armOperation : c.operation = a.operation) :
    checkedCatch
      (callbackSlice e n u x (requestKey table r) e.permission active installation)
      (requestKey table r) (consumerKey table c) e.permission =
      some ⟨requestKey table r, consumerKey table c, e.permission⟩ := by
  have useChecked : checkedUse e n u = some u := by
    simp only [checkedUse, ite_eq_left useJoins]
  have portReady : PortReady
      (callbackSlice e n u x (requestKey table r) e.permission active installation)
      (requestKey table r) e.permission := by
    apply Or.inl
    exact ⟨e, by simp [callbackSlice], n, by simp [callbackSlice],
      u, by simp [callbackSlice], x, by simp [callbackSlice],
      rfl, useChecked, handle, view, receipt, origin⟩
  have familyKey : (requestKey table r).operation.family ∈ e.permission.families := by
    rw [row]
    exact encoded_family_member table family
  have ready : CatchReady
      (callbackSlice e n u x (requestKey table r) e.permission active installation)
      (requestKey table r) (consumerKey table c) e.permission := by
    refine ⟨by simp [callbackSlice], by simp [callbackSlice], live, owner,
      familyKey, portReady, ?_, event, payload, installation,
      by simp [callbackSlice], handler, catchSite, installationOwner,
      armKey table a, armMember, arm, armSite, ?_⟩
    · exact congrArg (operationKey table) operation
    · exact congrArg (operationKey table) armOperation
  simp only [checkedCatch, ite_eq_left ready]

/-!
Parent application: callback_checked_catch supplies the finite R26 consumer
result for one shared bundle once all stated joins hold. operation_round_trip
and operationKey_injective justify using finite numeric coordinates for complete
structural operation identities on the covered snapshot. No membership, source
annotation, direct Name/Apply provenance, actual request emission, dynamic Catch
extraction, native Grant, or History is constructed here. The first remaining
premise belongs to the native extraction lane: authenticate these coordinates,
identity atoms, table coverage, request-owned observations and guard lookups from
one frozen execution snapshot. Original source-preservation §§1,3,5, corrected
birth-level qualification §§2–6, remains open for the full original language,
scopes and shared strategy, with principality/progress/termination unchanged.
-/
end YulangClosure.NativeCallbackGrantBridgeR31
