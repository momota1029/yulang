import YulangClosure.OriginalValueEntryDemand

/-!
Constructor data refinement for machine.rs Callee/allocate/direct_formal_root
and receiving.rs delay. This is a representation of the indicated Rust data
operations, not a Rust verification or a frontend/source interpretation theorem.
Program labels and decoded syntax are retained separately; decoding a source
program into this program table remains the frontend owner's obligation.
Unrepresented executable/Value kinds are opaque, not rejected source forms.
-/
namespace YulangClosure.OriginalCalleeDelayProvenance

open OriginalSource NativeClosureEnvironment SourceIdentityWorld OriginalWorldReadout

inductive ViewKind where
  | ordinary
  | retained (tag : Nat)
  deriving DecidableEq

structure Metadata where
  image : Option Nat
  unknown : Bool
  kind : ViewKind

inductive ValueKind where
  | computation
  | retained (tag : Nat)

structure RuntimeValue where
  source : Site
  kind : ValueKind

inductive Instruction where
  | parameterExecute (parameter : Name)
  | retained

structure Code where
  body : Source .expression
  instruction : Instruction

inductive Executable (Schema : Type) where
  | closure (closure : OriginalValueEntryDemand.Closure Schema)
  | delay (label environment : Nat)
  | retained (value : OriginalValueEntryDemand.Executable Schema)

variable {C Dict E Rest Schema : Type}

/-- The skeleton holds the other fields of the established suffix projection.
Its shadow executable/view fields are overwritten by project and never read.
The concrete values and views are dense lists; the executable map is sparse. -/
structure Raw (C Dict Rest Schema : Type) where
  values : List RuntimeValue
  views : List (View Nat Metadata)
  executables : Nat → Option (Executable Schema)
  program : Nat → Option Code
  skeleton : OriginalValueEntryDemand.Machine C Dict Metadata Rest Schema

local notation "R" => Raw C Dict Rest Schema
local notation "M" => OriginalValueEntryDemand.Machine C Dict Metadata Rest Schema

def executable (r : R) (handle : Nat) : Option (OriginalValueEntryDemand.Executable Schema) :=
  (r.executables handle).map fun value => match value with
    | .closure closure => .closure closure
    | .delay label environment => match r.program label with
      | some code => .delay code.body environment
      | none => .unrepresented
    | .retained value => value

def project (r : R) : M :=
  {r.skeleton with
    executables := executable r
    world := {r.skeleton.world with receiving :=
      {r.skeleton.world.receiving with views := vectorStore (r.views.map some)}}}

/-- Compositional representation relation, not a free operational law. -/
def Represents (r : R) (m : M) : Prop := m = project r

def allocate (r : R) (site : Site) (label environment : Nat) : R :=
  {r with
    values := r.values ++ [⟨site, .computation⟩]
    executables := fun handle => if handle = r.values.length
      then some (.delay label environment) else r.executables handle}

/-- Actual instruction -> parameter binder walk -> initialized cell -> role test.
The Arena walk has the previously proved native correspondence only on Valid
older-parent arenas. No receipt or dictionary dispatch occurs here. -/
def directFormalRoot (r : R) (label environment : Nat) : Option Nat := do
  let code ← r.program label
  let parameter ← match code.instruction with
    | .parameterExecute parameter => some parameter
    | .retained => none
  let cell ← lookupKey parameter r.skeleton.world.environments environment
  let received ← r.skeleton.world.cells.cell cell
  if received.interface = .computation then some received.view else none

/-- Invalid inherited handles are a direct-index panic boundary in Rust,
not a native RuntimeUnavailable result. Allocation has already happened. -/
inductive Boundary where
  | inheritedViewIndex
  | providerValueIndex

def delayMetadata (r : R) (inherited : Option Nat) : Option Metadata :=
  match inherited with
  | none => some ⟨none, true, .ordinary⟩
  | some handle => ((vectorStore (r.views.map some)).cell handle).map
      (fun view => ⟨view.data.image, view.data.unknown, .ordinary⟩)

def appendView (r : R) (handle : Nat) (data : Metadata) : R :=
  {r with views := r.views ++ [⟨handle, data⟩]}

/-- Preparation is before executable selection, even on later entry failure. -/
def prepare (r : R) (site : Site) (label environment : Nat) : R × Except Boundary Nat :=
  let allocated := allocate r site label environment
  match delayMetadata allocated (directFormalRoot allocated label environment) with
  | none => (allocated, .error .inheritedViewIndex)
  | some data => (appendView allocated r.values.length data, .ok r.views.length)

/-- The abstract append is derived from dense-list append, with every other
world field (including the complete receipt store/index) unchanged. -/
theorem append_view_refines (r : R) (handle : Nat) (data : Metadata) :
    Represents (appendView r handle data)
      {project r with world := {(project r).world with receiving :=
        {(project r).world.receiving with views :=
          (project r).world.receiving.views.push ⟨handle, data⟩}}} := by
  unfold Represents project appendView
  simp only [List.map_append, List.map_cons, List.map_nil, vector_store_push]
  rfl

/-- All post-allocation operands come from allocate, not Allocation's optional
closure store and not independently supplied Delay/view records. -/
theorem allocate_facts (r : R) (site : Site) (label environment : Nat)
    (code : Code) (decoded : r.program label = some code) :
    (allocate r site label environment).values.length = r.values.length + 1 ∧
    (vectorStore ((allocate r site label environment).values.map some)).cell r.values.length =
      some ⟨site, .computation⟩ ∧
    (project (allocate r site label environment)).executables r.values.length =
      some (.delay code.body environment) ∧
    (allocate r site label environment).views = r.views ∧
    (project (allocate r site label environment)).world = (project r).world := by
  refine ⟨by simp [allocate], ?_, ?_, rfl, rfl⟩
  · simp only [allocate, List.map_append, List.map_cons, List.map_nil, vector_store_push]
    simpa only [vectorStore, List.length_map] using
      push_current (vectorStore (r.values.map some)) (⟨site, .computation⟩ : RuntimeValue)
  · simp [project, executable, allocate, decoded]

theorem allocate_preserves_old (r : R) (site : Site) (label environment handle : Nat)
    (old : handle < r.values.length) :
    (vectorStore ((allocate r site label environment).values.map some)).cell handle =
      (vectorStore (r.values.map some)).cell handle ∧
    (allocate r site label environment).executables handle = r.executables handle ∧
    r.values.length ≠ handle := by
  refine ⟨?_, ?_, (Nat.ne_of_lt old).symm⟩
  · simpa only [allocate, List.map_append, List.map_cons, List.map_nil,
      vector_store_push] using push_old (vectorStore (r.values.map some))
        (⟨site, .computation⟩ : RuntimeValue) handle (by simpa [vectorStore] using old)
  · simp [allocate, Nat.ne_of_lt old]

theorem direct_formal_path (r : R) (label environment cell : Nat) (code : Code)
    (parameter : Name) (received : Received Nat)
    (decoded : r.program label = some code)
    (instruction : code.instruction = .parameterExecute parameter)
    (looked : lookupKey parameter r.skeleton.world.environments environment = some cell)
    (initialized : r.skeleton.world.cells.cell cell = some received) :
    directFormalRoot r label environment =
      if received.interface = .computation then some received.view else none := by
  simp [directFormalRoot, decoded, instruction, looked, initialized]

theorem allocate_keeps_formal_path (r : R) (site : Site) (label environment : Nat) :
    directFormalRoot (allocate r site label environment) label environment =
      directFormalRoot r label environment := rfl

theorem inherited_metadata (r : R) (handle : Nat) (view : View Nat Metadata)
    (found : (vectorStore (r.views.map some)).cell handle = some view) :
    delayMetadata r (some handle) = some ⟨view.data.image, view.data.unknown, .ordinary⟩ := by
  simp [delayMetadata, found]

theorem default_metadata (r : R) :
    delayMetadata r none = some ⟨none, true, .ordinary⟩ := rfl

/-- Complete preparation refinement, conditional only on the raw inheritance
read, not on a simulation/evaluation or an independently supplied Delay. -/
theorem prepare_refines (r : R) (site : Site) (label environment : Nat) (data : Metadata)
    (read : delayMetadata r (directFormalRoot r label environment) = some data) :
    prepare r site label environment =
      (appendView (allocate r site label environment) r.values.length data, .ok r.views.length) ∧
    Represents (prepare r site label environment).1
      (project (appendView (allocate r site label environment) r.values.length data)) := by
  have read' : delayMetadata (allocate r site label environment)
      (directFormalRoot (allocate r site label environment) label environment) = some data := read
  simp only [prepare, read']
  exact ⟨by trivial, rfl⟩

theorem prepared_view (r : R) (site : Site) (label environment : Nat) (data : Metadata) :
    let post := appendView (allocate r site label environment) r.values.length data
    (project post).world.receiving.views.cell r.views.length = some ⟨r.values.length, data⟩ ∧
    (project post).world.receiving.views.size = r.views.length + 1 ∧
    (project post).world.receiving.receipts = (project r).world.receiving.receipts ∧
    (project post).world.receiving.index = (project r).world.receiving.index := by
  dsimp [project, appendView, allocate]
  simp only [List.map_append, List.map_cons, List.map_nil, vector_store_push]
  refine ⟨?_, ?_, by trivial, by trivial⟩
  · simpa only [vectorStore, List.length_map] using
      push_current (vectorStore (r.views.map some)) (⟨r.values.length, data⟩ : View Nat Metadata)
  · simp [Store.push, vectorStore]

theorem prepared_preserves_views (r : R) (site : Site) (label environment : Nat)
    (data : Metadata) (handle : Nat) (old : handle < r.views.length) :
    (project (appendView (allocate r site label environment) r.values.length data)).world.receiving.views.cell handle =
      (project r).world.receiving.views.cell handle := by
  simpa only [project, appendView, allocate, List.map_append, List.map_cons,
    List.map_nil, vector_store_push] using push_old (vectorStore (r.views.map some))
      (⟨r.values.length, data⟩ : View Nat Metadata) handle (by simpa [vectorStore] using old)

/-- Compose preparation with the existing *Closure* suffix. Other executable
branches retain the suffix projection boundary; this is not a theorem about
primitive, continuation, operation or Computation entry. The provider is read from the
callee's existing RuntimeValue, not a caller-supplied provider site. -/
def run (ops : OriginalValueEntryDemand.Operations Dict E) (r : R) (site : Site) (label environment : Nat)
    (received : Received Nat) : R × Except (Sum Boundary (OriginalValueEntryDemand.Failure E)) Unit :=
  let (prepared, result) := prepare r site label environment
  match result with
  | .error boundary => (prepared, .error (.inl boundary))
  | .ok _ =>
    match (vectorStore (prepared.values.map some)).cell received.value with
    | none => (prepared, .error (.inl .providerValueIndex))
    | some provider =>
      let (post, result) := OriginalValueEntryDemand.invoke ops (project prepared) site provider.source received r.values.length
      ({prepared with skeleton := post}, result.mapError Sum.inr)

/-- The same allocated handle enters the accepted suffix, for *any* decoded
argument syntax. Neither a free Delay handle nor a free view is an operand. -/
theorem allocated_value_prefix (ops : OriginalValueEntryDemand.Operations Dict E) (r : R)
    (site : Site) (label environment : Nat) (code : Code) (data : Metadata)
    (received : Received Nat) (provider : RuntimeValue) (closure : OriginalValueEntryDemand.Closure Schema)
    (decoded : r.program label = some code)
    (read : delayMetadata r (directFormalRoot r label environment) = some data)
    (old : received.value < r.values.length)
    (provided : (vectorStore (r.values.map some)).cell received.value = some provider)
    (selected : r.executables received.value = some (.closure closure))
    (value : closure.source.formal.entry = .value)
    (capacity : r.skeleton.nextReceiver < ops.receiverLimit)
    (plain : ops.dictionaries = false ∨ received.dispatch = none) :
    let prepared := appendView (allocate r site label environment) r.values.length data
    let start := project prepared
    let post := {OriginalValueEntryDemand.setup (OriginalValueEntryDemand.allocate start site provider.source) closure
      start.nextReceiver start.world.control.current closure.savedEnvironment with
      state := .evaluate code.body environment}
    run ops r site label environment received =
      ({prepared with skeleton := post}, .ok ()) := by
  dsimp only
  let prepared := appendView (allocate r site label environment) r.values.length data
  have prep := (prepare_refines r site label environment data read).1
  have prior := allocate_preserves_old r site label environment received.value old
  have found : (vectorStore (prepared.values.map some)).cell received.value = some provider :=
    prior.1.trans provided
  have target : (project prepared).executables received.value = some (.closure closure) := by
    simp [project, executable, prepared, appendView, allocate, Nat.ne_of_lt old, selected]
  have argument : (project prepared).executables r.values.length = some (.delay code.body environment) := by
    simp [project, executable, prepared, appendView, allocate, decoded]
  have sub : OriginalValueEntryDemand.substitute ops (OriginalValueEntryDemand.allocate (project prepared) site provider.source)
      closure.savedEnvironment received.dispatch =
      (OriginalValueEntryDemand.allocate (project prepared) site provider.source, .ok closure.savedEnvironment) := by
    simp [OriginalValueEntryDemand.substitute, plain]
  have forced : OriginalValueEntryDemand.invoke ops (project prepared) site provider.source received r.values.length =
      ({OriginalValueEntryDemand.setup (OriginalValueEntryDemand.allocate (project prepared) site provider.source) closure
        (project prepared).nextReceiver (project prepared).world.control.current closure.savedEnvironment with
        state := .evaluate code.body environment}, .ok ()) := by
    simp only [OriginalValueEntryDemand.invoke, target]
    have cap : (project prepared).nextReceiver < ops.receiverLimit := capacity
    simp only [cap, ↓reduceIte, sub, value]
    simp [OriginalValueEntryDemand.execute, OriginalValueEntryDemand.setup, OriginalValueEntryDemand.allocate, argument, OriginalValueEntryDemand.substitute_none]
  dsimp only [prepared] at found forced
  simp only [run, prep, found, forced, Except.mapError]

/-- Transport the composed constructor result through the data representation.
This is the pre-Force demand poststate, including its exact view and complete
receipt store/index. There is no assumed native/source simulation law. -/
theorem allocated_demand_represents (ops : OriginalValueEntryDemand.Operations Dict E) (r : R)
    (site : Site) (label environment : Nat) (code : Code) (data : Metadata)
    (received : Received Nat) (provider : RuntimeValue) (closure : OriginalValueEntryDemand.Closure Schema)
    (decoded : r.program label = some code)
    (read : delayMetadata r (directFormalRoot r label environment) = some data)
    (old : received.value < r.values.length)
    (provided : (vectorStore (r.values.map some)).cell received.value = some provider)
    (selected : r.executables received.value = some (.closure closure))
    (value : closure.source.formal.entry = .value)
    (capacity : r.skeleton.nextReceiver < ops.receiverLimit)
    (plain : ops.dictionaries = false ∨ received.dispatch = none) :
    let prepared := appendView (allocate r site label environment) r.values.length data
    let start := project prepared
    let demand := {OriginalValueEntryDemand.setup
      (OriginalValueEntryDemand.allocate start site provider.source) closure start.nextReceiver
      start.world.control.current closure.savedEnvironment with state := .evaluate code.body environment}
    Represents (run ops r site label environment received).1 demand ∧
    demand.world.receiving = start.world.receiving ∧
    demand.world.receiving.views.cell r.views.length = some ⟨r.values.length, data⟩ ∧
    demand.world.receiving.receipts = (project r).world.receiving.receipts ∧
    demand.world.receiving.index = (project r).world.receiving.index := by
  dsimp only
  rw [allocated_value_prefix ops r site label environment code data received provider closure
    decoded read old provided selected value capacity plain]
  refine ⟨rfl, rfl, (prepared_view r site label environment data).1, rfl, rfl⟩

/-- Dictionary failure is after Delay value/view preparation and receiver
allocation. Its post-dictionary state survives, without pushing entry frames.
The dictionary engine's raw compose equation retains its existing owner. -/
theorem dictionary_failure_order (ops : OriginalValueEntryDemand.Operations Dict E) (r : R)
    (site : Site) (label environment : Nat) (data : Metadata)
    (received : Received Nat) (provider : RuntimeValue) (closure : OriginalValueEntryDemand.Closure Schema)
    (node : Node Name (OriginalValueEntryDemand.Dispatch C)) (changed : Dict) (error : E)
    (read : delayMetadata r (directFormalRoot r label environment) = some data)
    (old : received.value < r.values.length)
    (provided : (vectorStore (r.values.map some)).cell received.value = some provider)
    (selected : r.executables received.value = some (.closure closure))
    (capacity : r.skeleton.nextReceiver < ops.receiverLimit)
    (enabled : ops.dictionaries = true) (present : received.dispatch ≠ none)
    (found : nodeAt r.skeleton.world.environments closure.savedEnvironment = some node)
    (failed : ops.compose node.dispatch.substitution received.dispatch r.skeleton.dictionary =
      (changed, .error error)) :
    let prepared := appendView (allocate r site label environment) r.values.length data
    run ops r site label environment received =
      ({prepared with skeleton := {OriginalValueEntryDemand.allocate (project prepared) site provider.source
        with dictionary := changed}}, .error (.inr (.dictionary error))) := by
  dsimp only
  let prepared := appendView (allocate r site label environment) r.values.length data
  have prep := (prepare_refines r site label environment data read).1
  have prior := allocate_preserves_old r site label environment received.value old
  have provided' : (vectorStore (prepared.values.map some)).cell received.value = some provider :=
    prior.1.trans provided
  have selected' : (project prepared).executables received.value = some (.closure closure) := by
    simp [project, executable, prepared, appendView, allocate, Nat.ne_of_lt old, selected]
  have failure := OriginalValueEntryDemand.dictionary_failure_after_allocation ops (project prepared)
    closure site provider.source received r.values.length node changed error selected' capacity enabled
    present found failed
  dsimp only [prepared] at provided' failure
  simp only [run, prep, provided', failure, Except.mapError]

/-- Missing inherited view stops after value/executable allocation, before
view append, invocation allocation, dictionary substitution or frame setup. -/
theorem inherited_failure_order (ops : OriginalValueEntryDemand.Operations Dict E) (r : R)
    (site : Site) (label environment : Nat) (received : Received Nat)
    (missing : delayMetadata r (directFormalRoot r label environment) = none) :
    run ops r site label environment received =
      (allocate r site label environment, .error (.inl .inheritedViewIndex)) := by
  have missing' : delayMetadata (allocate r site label environment)
      (directFormalRoot (allocate r site label environment) label environment) = none := missing
  simp only [run, prepare, missing']

/-- Source receipt construction records the complete identity-bearing record.
This does not identify its world with a pre-Force native world. -/
theorem source_receipt_record (r : R) (entry : OriginalRecursivePair.EntryData Name Nat Site) :
    let before := OriginalRecursivePair.enterWorld (project r).world entry.call entry.provider
    (OriginalRecursivePair.receiveWorld before entry).receiving.receipts.cell
      before.receiving.receipts.size =
      some ⟨before.control.current, entry.carrier.view, entry.slot, some entry.formal⟩ :=
  (OriginalRecursivePair.source_receipt_fields _ _).1

/-- Appending the Delay's view retains every historical receipt and its index
exactly. This operation creates no receipt. -/
theorem preforce_receipts_unchanged (r : R) (site : Site) (label environment : Nat) (data : Metadata) :
    let prepared := appendView (allocate r site label environment) r.values.length data
    (project prepared).world.receiving.receipts = (project r).world.receiving.receipts ∧
    (project prepared).world.receiving.index = (project r).world.receiving.index := ⟨rfl, rfl⟩

end YulangClosure.OriginalCalleeDelayProvenance
