import YulangClosure.OriginalNameForceExtraction

/-!
Pre-Force Closure/Value-entry projection of machine.rs. This constructs raw
mutation order, not an original source judgment or a complete native simulation.
Source Parameter/code labels are retained data; their frontend correspondence
remains at the source owner. Dictionary `then` is an explicit raw operation,
including its poststate on failure, never a successful-substitution premise.
No callback entry or formal receipt is performed in this prefix.
-/
namespace YulangClosure.OriginalValueEntryDemand

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalParameterWorld OriginalFormalShared NativeClosureEnvironment SourceIdentityWorld

variable {s : Sorts} {C Dict E ViewData Rest Schema View : Type}

structure Dispatch (C : Type) where
  context : C
  substitution : Option Nat

structure Closure (Schema : Type) where
  source : Parameter
  unitPattern : Bool
  recordPattern : Option (List Name)
  rootSchema : Option Schema
  callbackSchema : Option Schema
  savedEnvironment : Nat

inductive Executable (Schema : Type) where
  | closure (closure : Closure Schema)
  | delay (code : Source .expression) (environment : Nat)
  | other
  | unrepresented

inductive Frame (Schema : Type) where
  | receiverReturn (activation : Nat) (previous : Owner)
  | valueEntry (closure : Closure Schema) (entryReceiver environment : Nat)

inductive ControlState where
  | other
  | evaluate (code : Source .expression) (environment : Nat)

structure Machine (C Dict ViewData Rest Schema : Type) where
  world : World Name (Dispatch C) Nat ViewData Site Rest
  dictionary : Dict
  nextReceiver : Nat
  frames : List (Frame Schema)
  executables : Nat → Option (Executable Schema)
  state : ControlState

inductive Failure (E : Type) where
  | identityExhausted
  /-- Total projection marker for Rust's direct environment-index panic boundary;
  this is not claimed to be a native RuntimeUnavailable result. -/
  | invalidEnvironment
  | dictionary (error : E)
  | expectedCallable
  | expectedComputation
  /-- A projection boundary, NOT a RuntimeUnavailable or rejected source form. -/
  | outsideProjection

/- This unproved owner interface retains both native dictionary outcomes. It
does not establish that any particular Rust dictionary engine realizes it. -/
structure Operations (Dict E : Type) where
  dictionaries : Bool
  receiverLimit : Nat
  compose : Option Nat → Option Nat → Dict → Dict × Except E (Option Nat)

local notation "M" => Machine C Dict ViewData Rest Schema

def allocate (m : M) (call provider : Site) : M :=
  let control : Control Site :=
    ⟨m.world.control.invocations.push ⟨call, provider, true⟩,
      m.nextReceiver :: m.world.control.active, .invocation m.nextReceiver⟩
  { m with
    nextReceiver := m.nextReceiver + 1
    world := {m.world with control := control} }

def substitute (ops : Operations Dict E) (m : M) (environment : Nat)
    (substitution : Option Nat) : M × Except (Failure E) Nat :=
  if ops.dictionaries = false ∨ substitution = none then (m, .ok environment)
  else match nodeAt m.world.environments environment with
    | none => (m, .error .invalidEnvironment)
    | some node =>
      let (dictionary, result) := ops.compose node.dispatch.substitution substitution m.dictionary
      let changed := {m with dictionary := dictionary}
      match result with
      | .error error => (changed, .error (.dictionary error))
      | .ok composed =>
        let environments := Arena.append m.world.environments environment none
          {node.dispatch with substitution := composed}
        ({changed with world := {changed.world with environments := environments}},
         .ok m.world.environments.size)

def setup (m : M) (closure : Closure Schema) (receiver : Nat) (previous : Owner)
    (environment : Nat) : M :=
  {m with frames := .valueEntry closure receiver environment ::
    .receiverReturn receiver previous :: m.frames}

def execute (ops : Operations Dict E) (m : M) (argument : Nat) : M × Except (Failure E) Unit :=
  match m.executables argument with
  | some (.delay code environment) =>
      let (next, result) := substitute ops m environment none
      match result with
      | .error error => (next, .error error)
      | .ok saved => ({next with state := .evaluate code saved}, .ok ())
  | some .unrepresented => (m, .error .outsideProjection)
  | _ => (m, .error .expectedComputation)

/- The incoming receiver dispatch affects the Closure's captured environment.
The Delay execute call is a distinct operation with substitution None. -/
def invoke (ops : Operations Dict E) (m : M) (call provider : Site)
    (received : Received Nat) (argument : Nat) : M × Except (Failure E) Unit :=
  match m.executables received.value with
  | some (.closure closure) =>
    if m.nextReceiver < ops.receiverLimit then
      let allocated := allocate m call provider
      let (changed, result) := substitute ops allocated closure.savedEnvironment received.dispatch
      match result with
      | .error error => (changed, .error error)
      | .ok environment =>
        match closure.source.formal.entry with
        | .value => execute ops (setup changed closure m.nextReceiver m.world.control.current environment) argument
        | .computation => (changed, .error .outsideProjection)
    else (m, .error .identityExhausted)
  | some .unrepresented => (m, .error .outsideProjection)
  | _ => (m, .error .expectedCallable)

/- Full original CallInput is retained, independently of the raw machine
projection. Merely putting these operands together proves no readout law. -/
structure Request (s : Sorts) where
  call : CallInput s
  receiver : Received Nat
  argument : Received Nat
  sourceCall : Site
  sourceProvider : Site

def Request.run (request : Request s) (ops : Operations Dict E) (m : M) :=
  (request.call, invoke ops m request.sourceCall request.sourceProvider
    request.receiver request.argument.value)

theorem request_keeps_full_call (request : Request s) (ops : Operations Dict E) (m : M) :
    (request.run ops m).1 = request.call := rfl

theorem substitute_none (ops : Operations Dict E) (m : M) (environment : Nat) :
    substitute ops m environment none = (m, .ok environment) := by
  simp [substitute]

theorem execute_same_delay (ops : Operations Dict E) (m : M)
    (delay : OriginalIdentityCarrier.NameDelay)
    (found : m.executables delay.handle = some (.delay delay.code delay.environment)) :
    execute ops m delay.handle =
      ({m with state := .evaluate delay.code delay.environment}, .ok ()) := by
  simp [execute, found, substitute_none]

theorem allocated_receiver (m : M) (call provider : Site)
    (aligned : m.nextReceiver = m.world.control.invocations.size) :
    (allocate m call provider).world.control.current = .invocation m.nextReceiver ∧
    (allocate m call provider).world.control.invocations.cell m.nextReceiver =
      some ⟨call, provider, true⟩ ∧
    (allocate m call provider).world.control.active = m.nextReceiver :: m.world.control.active ∧
    (allocate m call provider).world.receiving = m.world.receiving := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simpa only [allocate, aligned] using push_current m.world.control.invocations ⟨call, provider, true⟩

/- No successful invocation/Force prefix is supplied. Raw lookup, Value role
and finite receiver capacity are the actual branch checks. The general
dictionary branch remains in invoke and substitute, with its original owner. -/
theorem value_delay_prefix (ops : Operations Dict E) (m : M)
    (closure : Closure Schema) (delay : OriginalIdentityCarrier.NameDelay)
    (call provider : Site) (received : Received Nat)
    (selected : m.executables received.value = some (.closure closure))
    (argument : m.executables delay.handle = some (.delay delay.code delay.environment))
    (value : closure.source.formal.entry = .value)
    (capacity : m.nextReceiver < ops.receiverLimit)
    (plain : ops.dictionaries = false ∨ received.dispatch = none) :
    invoke ops m call provider received delay.handle =
      ({setup (allocate m call provider) closure m.nextReceiver m.world.control.current
          closure.savedEnvironment with state := .evaluate delay.code delay.environment}, .ok ()) := by
  have sub : substitute ops (allocate m call provider) closure.savedEnvironment received.dispatch =
      (allocate m call provider, .ok closure.savedEnvironment) := by simp [substitute, plain]
  simp only [invoke, selected, capacity, ↓reduceIte, sub, value]
  exact execute_same_delay ops _ delay argument

theorem prefix_operands (m : M) (closure : Closure Schema)
    (delay : OriginalIdentityCarrier.NameDelay) (call provider : Site) :
    let post := {setup (allocate m call provider) closure m.nextReceiver m.world.control.current
      closure.savedEnvironment with state := .evaluate delay.code delay.environment}
    post.frames = .valueEntry closure m.nextReceiver closure.savedEnvironment ::
      .receiverReturn m.nextReceiver m.world.control.current :: m.frames ∧
    post.world.receiving = m.world.receiving ∧ post.world.cells = m.world.cells ∧
    post.state = .evaluate delay.code delay.environment ∧ post.dictionary = m.dictionary :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/- Failure is stateful: allocation has happened before dictionary composition,
and the failed dictionary operation's poststate is retained, with no frames. -/
theorem dictionary_failure_after_allocation (ops : Operations Dict E) (m : M)
    (closure : Closure Schema) (call provider : Site) (received : Received Nat) (argument : Nat)
    (node : Node Name (Dispatch C)) (changed : Dict) (error : E)
    (selected : m.executables received.value = some (.closure closure))
    (capacity : m.nextReceiver < ops.receiverLimit)
    (enabled : ops.dictionaries = true) (present : received.dispatch ≠ none)
    (found : nodeAt m.world.environments closure.savedEnvironment = some node)
    (failed : ops.compose node.dispatch.substitution received.dispatch m.dictionary = (changed, .error error)) :
    invoke ops m call provider received argument =
      ({allocate m call provider with dictionary := changed}, .error (.dictionary error)) := by
  simp [invoke, selected, capacity, substitute, enabled, present, allocate, found, failed]

theorem execute_failure_keeps_frames (ops : Operations Dict E) (m : M) (argument : Nat)
    (absent : m.executables argument = none) :
    execute ops m argument = (m, .error .expectedComputation) := by
  simp [execute, absent]

theorem dictionary_success_environment (ops : Operations Dict E) (m : M)
    (environment : Nat) (substitution : Option Nat) (node : Node Name (Dispatch C))
    (changed : Dict) (composed : Option Nat)
    (enabled : ops.dictionaries = true) (present : substitution ≠ none)
    (found : nodeAt m.world.environments environment = some node)
    (result : ops.compose node.dispatch.substitution substitution m.dictionary = (changed, .ok composed)) :
    let environments := Arena.append m.world.environments environment none
      (⟨node.dispatch.context, composed⟩ : Dispatch C)
    substitute ops m environment substitution =
      ({m with dictionary := changed, world := {m.world with environments := environments}}, .ok m.world.environments.size) := by
  simp [substitute, enabled, present, found, result]

/- The descriptor is tracked ONLY through the existing selected-contract Return
constructor. This theorem does not assert that this packet executes a Return,
or identify that source-selected contract with a native Name-cell readout. -/
theorem selected_return_constructor (closure : Closure Schema)
    (selection : Selected s View closure.source)
    (mode : closure.source.formal.entry = .value)
    (assignment : OriginalWorldReadout.ViewAssignment s Nat) (m : M)
    (raw : Received Nat) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) :
    let evidence := nativeEvidence closure.source selection mode assignment m.world raw
      observation after endpoints bindings witness
    evidence.address = m.world.cells.size ∧
    evidence.data.installed = .value (selection.valueDescriptor mode)
      (assignment.value raw.value) (assignment.root raw.value) :=
  ⟨rfl, native_evidence_object closure.source selection mode assignment m.world raw
    observation after endpoints bindings witness⟩

/- This is a precise representation mismatch, not a source counterexample:
the original source constructor mints a receipt before Force; native plain
Value entry has not minted one. Callback entry cannot repair that past event. -/
theorem source_receipt_not_native_prefix (m : M) (closure : Closure Schema)
    (delay : OriginalIdentityCarrier.NameDelay) (entry : OriginalRecursivePair.EntryData Name Nat Site) :
    let native := {setup (allocate m entry.call entry.provider) closure m.nextReceiver
      m.world.control.current closure.savedEnvironment with state := .evaluate delay.code delay.environment}
    let source := OriginalRecursivePair.receiveWorld
      (OriginalRecursivePair.enterWorld m.world entry.call entry.provider) entry
    native.world.receiving.receipts.size ≠ source.receiving.receipts.size := by
  dsimp [setup, allocate, OriginalRecursivePair.receiveWorld, OriginalRecursivePair.enterWorld,
    Receiving.record, Store.push]
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

theorem actual_value_entry_receipt_gap (ops : Operations Dict E) (m : M)
    (closure : Closure Schema) (delay : OriginalIdentityCarrier.NameDelay)
    (entry : OriginalRecursivePair.EntryData Name Nat Site) (received : Received Nat)
    (selected : m.executables received.value = some (.closure closure))
    (argument : m.executables delay.handle = some (.delay delay.code delay.environment))
    (value : closure.source.formal.entry = .value)
    (capacity : m.nextReceiver < ops.receiverLimit)
    (plain : ops.dictionaries = false ∨ received.dispatch = none) :
    (invoke ops m entry.call entry.provider received delay.handle).1.world.receiving.receipts.size ≠
      (OriginalRecursivePair.receiveWorld
        (OriginalRecursivePair.enterWorld m.world entry.call entry.provider) entry).receiving.receipts.size := by
  rw [value_delay_prefix ops m closure delay entry.call entry.provider received selected argument value capacity plain]
  exact source_receipt_not_native_prefix m closure delay entry

/- Source receipt admission is consumed only at its existing source boundary.
This is the unchanged source theorem, with no native demand/event conclusion. -/
theorem source_call_recovery (operator : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (parameter : Parameter) (invocation receipt : ScopedValue (Payload s View))
    (invocationAdmitted : Admitted operator readout admissions environment (invocationBinder parameter) invocation)
    (receiptAdmitted : Admitted operator readout admissions
      (environment.extend (invocationBinder parameter) invocation) (receiptBinder parameter) receipt)
    (state : Decoded s View)
    (decoded : decode readout ((environment.extend (invocationBinder parameter) invocation).extend
      (receiptBinder parameter) receipt) = some state) :
    ∃ (before : Decoded s View) (raw : OriginalSourceEnvironment.Invocation s View),
      decode readout environment = some before ∧ invocation.data = .runtime (.invocation raw) ∧
      CheckedDomain operator (raw.challenge
        (readout.event before.fixedFrames before.assignment.event (invocationBinder parameter) (.invocation raw))
        (before.callRow (invocationBinder parameter)).descriptor before.viewMeaning) ∧
      state.active = some ((raw.challenge
        (readout.event before.fixedFrames before.assignment.event (invocationBinder parameter) (.invocation raw))
        (before.callRow (invocationBinder parameter)).descriptor before.viewMeaning).input) ∧
      state.assignment.descriptor = before.assignment.descriptor :=
  OriginalIdentityRealization.receipt_recovers_call operator readout admissions environment parameter
    invocation receipt invocationAdmitted receiptAdmitted state decoded

end YulangClosure.OriginalValueEntryDemand
