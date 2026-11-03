import YulangClosure.OriginalCalleeDelayProvenance
import YulangClosure.OriginalScopedClosure

/-!
R312: a source-indexed Apply/Callee/Delay data refinement and initialized Name
readback. Authority: selected EI §§3.1–3.4, machine.rs Apply and Callee branches.
This is a representation of those constructors, not a Rust simulation or an
EI interpretation. The external callee transition relation retains its owner.
Unrepresented executable/code kinds remain present. No source typing, whole
History, NativeExtraction, carrier Meaning or successful Force is an input.

`Surrounding` below lists exactly the still independent world/license/future
leaves. It has no concrete instance here. Its conditional parent application
must not be reported as original Call admission or whole-language closure.
-/
namespace YulangClosure.OriginalCalleeArgumentHistoryR312

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking OriginalWorldReadout
open OriginalParameterSemantics NativeClosureEnvironment SourceIdentityWorld


variable {C Dict Rest Schema : Type}

/-- All original scoped Program constructors remain traversable. This small
structural path avoids importing unrelated inference proofs just to authenticate
one source occurrence; it neither drops a scope nor generates a new owner. -/
def children : Program → List Program
  | .rule _ _ _ _ _ children => forestChildren children
  | .existsE _ body | .forallE _ body | .initializerE _ _ body
  | .executionE _ body | .sharedE _ body | .publishGroup _ _ body
  | .atPublication _ _ body | .aliasPublication _ _ _ body => [body]
  | .choice _ _ left right => [left, right]
where
  forestChildren : Programs → List Program
    | .nil => []
    | .cons head tail => head :: forestChildren tail

inductive Occurs : Program → Program → Prop where
  | root (program) : Occurs program program
  | descend {outer child selected} : child ∈ children outer → Occurs child selected →
      Occurs outer selected

/-- The full original rule, both arbitrary scoped children and every premise
are retained. Position includes declaration, route, telescope and frame. -/
structure CallOccurrence where
  position : Position
  site : Site
  context : Context
  premises : List Premise
  callee : Program
  argument : Program

def CallOccurrence.program (call : CallOccurrence) : Program :=
  .rule call.position .app call.site call.context call.premises
    (.cons call.callee (.cons call.argument .nil))

/-- Actual scoped source occurrence plus a frontend code-label representation
edge. No successful argument execution, typing or guard proof is supplied. -/
structure ApplySource (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) where
  origin : Declaration
  rootContext : Context
  root : Source .expression
  call : CallOccurrence
  present : Occurs (source origin rootContext root) call.program
  calleeLabel : Nat
  argumentLabel : Nat
  argumentCode : OriginalCalleeDelayProvenance.Code
  decoded : r.program argumentLabel = some argumentCode
  originalArgument : call.argument.erase = sourceRules call.context argumentCode.body

/-- The whole occurrence, both labels and caller environment survive the
callee. These source fields are ghost data, not invented runtime owners. -/
structure SavedCallee where
  call : CallOccurrence
  calleeLabel : Nat
  argumentLabel : Nat
  callerEnvironment : Nat

def ApplySource.save (a : ApplySource r) (caller : Nat) : SavedCallee :=
  ⟨a.call, a.calleeLabel, a.argumentLabel, caller⟩

inductive Control where
  | evaluate (label environment : Nat)
  | returned (raw : Received Nat)
  | request (token : Nat)
  | retained (tag : Nat)

inductive Frame where
  | callee (saved : SavedCallee)
  | retained (tag : Nat)

structure Machine (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) where
  control : Control
  frames : List Frame

/-- machine.rs Instruction::Apply: save first, evaluate only the callee. -/
def enter (a : ApplySource r) (caller : Nat) (frames : List Frame) : Machine r :=
  ⟨.evaluate a.calleeLabel caller, .callee (a.save caller) :: frames⟩

theorem enter_saves_original (a : ApplySource r) (caller : Nat) (frames : List Frame) :
    (enter a caller frames).control = .evaluate a.calleeLabel caller ∧
    (enter a caller frames).frames = .callee (a.save caller) :: frames ∧
    (a.save caller).call = a.call ∧
    Occurs (source a.origin a.rootContext a.root) (a.save caller).call.program :=
  ⟨rfl, rfl, rfl, a.present⟩

/-- A callee's owned raw transition can include arbitrary Request/resume steps.
No transition law or successful Return is manufactured by this relation. -/
inductive Development (step : α → α → Prop) : α → α → Prop where
  | initial (state) : Development step state state
  | next {start before after} : Development step start before → step before after →
      Development step start after

/-- Lift only the callee's transitions while the saved frame waits. This does
not execute a pending argument or rerun a completed prefix on resume. -/
def suspended (saved : SavedCallee) (tail : List Frame) (state : α) :=
  (state, Frame.callee saved :: tail)

theorem development_keeps_saved (step : α → α → Prop) (saved : SavedCallee)
    (tail : List Frame) (start finish : α) (development : Development step start finish) :
    Development (fun before after : α × List Frame =>
      step before.1 after.1 ∧ after.2 = before.2)
      (suspended saved tail start) (suspended saved tail finish) := by
  induction development with
  | initial => exact .initial _
  | next prior transition ih => exact .next ih ⟨transition, rfl⟩

/-- Preparation is called only on an actual returned-control/top-Callee pair.
Its operands are read from the saved frame, with no caller-supplied Delay. -/
def returnTop (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (m : Machine r) :
    Option (SavedCallee × Received Nat × List Frame ×
      (OriginalCalleeDelayProvenance.Raw C Dict Rest Schema × Except OriginalCalleeDelayProvenance.Boundary Nat)) :=
  match m.control, m.frames with
  | .returned received, .callee saved :: tail =>
      some (saved, received, tail,
        OriginalCalleeDelayProvenance.prepare r saved.call.site saved.argumentLabel saved.callerEnvironment)
  | _, _ => none

theorem return_top_exact (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (saved : SavedCallee)
    (received : Received Nat) (tail : List Frame) :
    returnTop r ⟨.returned received, .callee saved :: tail⟩ =
      some (saved, received, tail,
        OriginalCalleeDelayProvenance.prepare r saved.call.site saved.argumentLabel saved.callerEnvironment) := rfl

theorem pending_does_not_prepare (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (token : Nat) (frames : List Frame) :
    returnTop r ⟨.request token, frames⟩ = none := rfl

/-- Exact Delay-only executable projection. Other executable kinds remain
opaque None; this projection is never used to reject those source forms.
Adapted from the complementary R312 CarrierBridgeProbe, with its authorship
retained in the handoff. -/
def delaySnapshot (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) :
    Store (Option (Closure (Source .expression))) :=
  ⟨r.values.length, fun handle => ((OriginalCalleeDelayProvenance.project r).executables handle).map fun executable =>
    match executable with
    | .delay body environment => some (capture environment body)
    | _ => none⟩

theorem allocated_delay_snapshot (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (site : Site) (label environment : Nat) (code : OriginalCalleeDelayProvenance.Code)
    (decoded : r.program label = some code) :
    (delaySnapshot (OriginalCalleeDelayProvenance.allocate r site label environment)).cell r.values.length =
      some (some (capture environment code.body)) := by
  have allocated := (OriginalCalleeDelayProvenance.allocate_facts r site label environment code decoded).2.2.1
  simp only [delaySnapshot, allocated, Option.map_some]

/-- Snapshot selection is derived at this actual cell, rather than from an
assumed whole-store equation to the carrier Allocation.after. -/
theorem owner_from_actual_cell {b : Sorts} {D ViewData Rest Body View : Type}
    (native : OriginalNameForceExtraction.Native b D ViewData Rest Body View)
    (input : CarrierInput (OriginalNameForceExtraction.S b D ViewData Rest Body View))
    (event : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)) (delay : OriginalIdentityCarrier.NameDelay)
    (handle : native.handle input.carrier = some delay.handle)
    (cell : (native.executables event).cell delay.handle = some (some delay.closure))
    (mode : OriginalNameForceExtraction.NameMode) (modeFound : native.nameMode event delay.handle = some mode)
    (lexical : mode.lexicalObserve = true) : OriginalNameForceExtraction.owner native input event = some delay := by
  simp only [OriginalNameForceExtraction.owner, handle, Option.bind_eq_bind, Option.bind_some, cell,
    modeFound, lexical, ite_true]
  cases delay
  rfl

/-- The prepared Name has the fresh actual value handle and saved caller
lexical environment. The original source Program, decode and Name code are
all checked at the same request; no pure-read generalization is asserted. -/
theorem prepared_name (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) (a : ApplySource r)
    (caller : Nat) (site : Site) (name : Name) (data : OriginalCalleeDelayProvenance.Metadata)
    (received : Received Nat) (tail : List Frame)
    (sourceName : a.argumentCode.body = .name ⟨site, none⟩ name)
    (read : OriginalCalleeDelayProvenance.delayMetadata r (OriginalCalleeDelayProvenance.directFormalRoot r a.argumentLabel caller) = some data) :
    let saved := a.save caller
    let post := OriginalCalleeDelayProvenance.appendView (OriginalCalleeDelayProvenance.allocate r saved.call.site
      saved.argumentLabel saved.callerEnvironment) r.values.length data
    returnTop r ⟨.returned received, .callee saved :: tail⟩ =
      some (saved, received, tail, (post, .ok r.views.length)) ∧
    (delaySnapshot post).cell r.values.length =
      some (some (OriginalIdentityCarrier.NameDelay.closure ⟨r.values.length, caller, name, site⟩)) ∧
    (OriginalCalleeDelayProvenance.project post).world.receiving.views.cell r.views.length =
      some ⟨r.values.length, data⟩ ∧
    a.call.argument.erase = sourceRules a.call.context (.name ⟨site, none⟩ name) := by
  dsimp only
  refine ⟨?_, ?_, (OriginalCalleeDelayProvenance.prepared_view r a.call.site a.argumentLabel caller data).1, ?_⟩
  · dsimp only [ApplySource.save]
    rw [return_top_exact, (OriginalCalleeDelayProvenance.prepare_refines r a.call.site
      a.argumentLabel caller data read).1]
  · have allocated := allocated_delay_snapshot r a.call.site a.argumentLabel
      caller a.argumentCode a.decoded
    change (delaySnapshot (OriginalCalleeDelayProvenance.allocate r a.call.site
      a.argumentLabel caller)).cell r.values.length = _
    simpa only [sourceName, OriginalIdentityCarrier.NameDelay.closure,
      OriginalIdentityCarrier.NameDelay.code] using allocated
  · rw [← sourceName]
    exact a.originalArgument

/-- Repeated use allocates a new carrier even with identical source code,
site, caller environment, and returned callee. A stale handle cannot replay it. -/
theorem repeated_call_fresh (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (site : Site) (label environment : Nat) :
    (OriginalCalleeDelayProvenance.allocate r site label environment).values.length ≠ r.values.length := by
  simp [OriginalCalleeDelayProvenance.allocate]


section NamePreparation

variable {b : Sorts} {Body View : Type}

abbrev S (b : Sorts) (C Rest Body View : Type) :=
  OriginalNameForceExtraction.S b (OriginalValueEntryDemand.Dispatch C)
    OriginalCalleeDelayProvenance.Metadata Rest Body View

/-- CalRet's raw snapshot and the source label edge are explicit representation
inputs. No callee Return typing, Function certificate or semantic world is
hidden in them. The return event is live, rather than a copied creation world. -/
structure Preparation (b : Sorts) (C Dict Rest Schema Body View : Type) where
  raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema
  apply : ApplySource raw
  caller : Nat
  name : Name
  nameSite : Site
  sourceName : apply.argumentCode.body = .name ⟨nameSite, none⟩ name
  data : OriginalCalleeDelayProvenance.Metadata
  read : OriginalCalleeDelayProvenance.delayMetadata raw
    (OriginalCalleeDelayProvenance.directFormalRoot raw apply.argumentLabel caller) = some data
  calRet : Event (S b C Rest Body View)
  aligned : calRet.current.world = (OriginalCalleeDelayProvenance.project raw).world

variable (p : Preparation b C Dict Rest Schema Body View)

def Preparation.saved : SavedCallee := p.apply.save p.caller

def Preparation.post : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema :=
  OriginalCalleeDelayProvenance.appendView
    (OriginalCalleeDelayProvenance.allocate p.raw p.apply.call.site
      p.apply.argumentLabel p.caller) p.raw.values.length p.data

def Preparation.delay : OriginalIdentityCarrier.NameDelay :=
  ⟨p.raw.values.length, p.caller, p.name, p.nameSite⟩

/-- This computes only the raw preparation world. Independent logical event
validity is deliberately absent; eta0, original history and shared witness are
retained, and no Force/Observe receipt is inserted. -/
def Preparation.event : Event (S b C Rest Body View) :=
  {p.calRet with current := {p.calRet.current with
    world := (OriginalCalleeDelayProvenance.project p.post).world}}

def Preparation.row (interface : b.Interface) : CarrierRow (S b C Rest Body View) :=
  ⟨interface, p.event.eta.views.carrier p.delay.handle,
    p.event.eta.views.root p.delay.handle, p.event⟩

def Preparation.allocation : OriginalIdentityCarrier.Allocation p.delay where
  before := (List.range p.raw.values.length).map fun handle => (delaySnapshot p.raw).cell handle |>.join
  fresh := by simp [Preparation.delay]

theorem prepared_allocation (received : Received Nat) (tail : List Frame) :
    returnTop p.raw ⟨.returned received, .callee p.saved :: tail⟩ =
      some (p.saved, received, tail, (p.post, .ok p.raw.views.length)) ∧
    (delaySnapshot p.post).cell p.delay.handle = some (some p.delay.closure) ∧
    p.delay.handle = p.raw.values.length ∧
    p.delay.environment = p.saved.callerEnvironment ∧
    p.apply.call.argument.erase =
      sourceRules p.apply.call.context p.delay.code := by
  have facts := prepared_name p.raw p.apply p.caller p.nameSite p.name p.data received tail
    p.sourceName p.read
  exact ⟨facts.1, facts.2.1, rfl, rfl, facts.2.2.2⟩

theorem preparation_event_fields :
    p.event.history = p.calRet.history ∧ p.event.fiber = p.calRet.fiber ∧
    p.event.eta0 = p.calRet.eta0 ∧ p.event.eta = p.calRet.eta ∧
    p.event.witness = p.calRet.witness ∧
    p.event.current.world.receiving.receipts = p.calRet.current.world.receiving.receipts ∧
    p.event.current.world.receiving.index = p.calRet.current.world.receiving.index := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [p.aligned]; rfl
  · rw [p.aligned]; rfl

theorem preparation_keeps_capture_data :
    p.event.current.world.environments = p.calRet.current.world.environments ∧
    p.event.current.world.cells = p.calRet.current.world.cells ∧
    ∀ handle, handle < p.raw.views.length →
      p.event.current.world.receiving.views.cell handle = p.calRet.current.world.receiving.views.cell handle := by
  refine ⟨?_, ?_, ?_⟩
  · rw [p.aligned]; rfl
  · rw [p.aligned]; rfl
  · intro handle old
    rw [p.aligned]
    exact OriginalCalleeDelayProvenance.prepared_preserves_views p.raw
      p.apply.call.site p.apply.argumentLabel p.caller p.data handle old

/-- The real bind supplies the lookup/cell/mode. Callee execution may extend
its lexical arena, but preservation of this cell and its old receiving view is
an explicit local callee-history leaf, not inferred from a source Name tag. -/
def capture_from_bound_caller
    (before : Event (S b C Rest Body View)) (parent : Nat) (raw : Received Nat)
    (node : Node Name (OriginalValueEntryDemand.Dispatch C))
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields (OriginalNameForceExtraction.Base b))
    (saved : p.caller = before.current.world.environments.size)
    (environments : Extends
      (bindEvent before parent p.name raw node found descriptor fields).current.world.environments
      p.calRet.current.world.environments)
    (stored : p.calRet.current.world.cells.cell before.current.world.cells.size = some raw.asValue)
    (matching : Matches p.calRet.current.world.receiving raw)
    (viewBound : raw.view < p.raw.views.length) :
    OriginalIdentityCarrier.CaptureAt p.delay p.event where
  address := before.current.world.cells.size
  raw := raw.asValue
  lookup := by
    rw [(preparation_keeps_capture_data p).1]
    change lookupKey p.name p.calRet.current.world.environments p.caller = _
    rw [saved]
    exact (lookup_history environments (fun name => decide (name = p.name))
      before.current.world.environments.size (Nat.lt_succ_self _)).trans
      (parameter_shadows before.current.world.environments parent
        before.current.world.cells.size p.name node.dispatch)
  stored := by rw [(preparation_keeps_capture_data p).2.1]; exact stored
  mode := rfl
  matching := by
    obtain ⟨view, present, same⟩ := matching
    exact ⟨view, ((preparation_keeps_capture_data p).2.2 raw.view viewBound).trans present, same⟩

theorem saved_environment_bound
    (before : Event (S b C Rest Body View)) (parent : Nat) (raw : Received Nat)
    (node : Node Name (OriginalValueEntryDemand.Dispatch C))
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields (OriginalNameForceExtraction.Base b))
    (saved : p.caller = before.current.world.environments.size)
    (environments : Extends
      (bindEvent before parent p.name raw node found descriptor fields).current.world.environments
      p.calRet.current.world.environments) :
    p.delay.environment < p.event.current.world.environments.size := by
  rw [(preparation_keeps_capture_data p).1]
  change p.caller < _
  rw [saved]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (extends_size environments)

/-- Ownership at this actual event follows from the computed fresh cell. Only
carrier-handle decoding and actual instruction mode remain native readouts. -/
theorem prepared_owner (native : OriginalNameForceExtraction.Native b
      (OriginalValueEntryDemand.Dispatch C) OriginalCalleeDelayProvenance.Metadata Rest Body View)
    (interface : b.Interface)
    (handle : native.handle (p.row interface).input.carrier = some p.delay.handle)
    (snapshot : native.executables p.event = delaySnapshot p.post)
    (mode : OriginalNameForceExtraction.NameMode)
    (modeFound : native.nameMode p.event p.delay.handle = some mode)
    (lexical : mode.lexicalObserve = true) :
    OriginalNameForceExtraction.owner native (p.row interface).input p.event = some p.delay := by
  apply owner_from_actual_cell native (p.row interface).input p.event p.delay handle _ mode modeFound lexical
  rw [snapshot]
  exact (prepared_allocation p (⟨0, .value, 0, none⟩ : Received Nat) []).2.1

/-- The actual provider source is read from the returned value vector; the
same raw CalRet observation/event supplies every returned logical field. This
constructor asserts no callee traceForm/Meaning or checked Function transport. -/
def Preparation.returned (observation : (OriginalNameForceExtraction.Base b).Observation)
    (received : Received Nat) (descriptor : b.Descriptor) (providers : Site → b.Provider) :
    Option (RawObservation (S b C Rest Body View) × ValueRow (S b C Rest Body View) × b.Provider) := do
  let provider ← (vectorStore (p.raw.values.map some)).cell received.value
  pure ⟨⟨observation, p.calRet⟩,
    ⟨descriptor, p.calRet.eta.views.value received.value, p.calRet.eta.views.root received.value, p.calRet⟩,
    providers provider.source⟩

theorem actual_return_same_event
    (observation : (OriginalNameForceExtraction.Base b).Observation) (received : Received Nat)
    (descriptor : b.Descriptor) (providers : Site → b.Provider)
    (provider : OriginalCalleeDelayProvenance.RuntimeValue)
    (provided : (vectorStore (p.raw.values.map some)).cell received.value = some provider) :
    p.returned observation received descriptor providers = some
      ⟨⟨observation, p.calRet⟩,
        ⟨descriptor, p.calRet.eta.views.value received.value,
          p.calRet.eta.views.root received.value, p.calRet⟩,
        providers provider.source⟩ := by
  simp only [Preparation.returned, provided]
  rfl


/-- Initialized native caller construction and the exact local preservation
leaves through callee evaluation. These are raw equations, not History or
carrier/trace Meaning. The vector premise excludes malformed Store addresses. -/
structure CallerBinding (b : Sorts) (D ViewData Rest Body View : Type) where
  before : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)
  parent : Nat
  raw : Received Nat
  node : Node Name D
  found : nodeAt before.current.world.environments parent = some node
  descriptor : b.Descriptor
  fields : EventFields (OriginalNameForceExtraction.Base b)

structure BoundCaller (p : Preparation b C Dict Rest Schema Body View) where
  binding : CallerBinding b (OriginalValueEntryDemand.Dispatch C)
    OriginalCalleeDelayProvenance.Metadata Rest Body View
  saved : p.caller = binding.before.current.world.environments.size
  environments : Extends
    (bindEvent binding.before binding.parent p.name binding.raw binding.node binding.found
      binding.descriptor binding.fields).current.world.environments
    p.calRet.current.world.environments
  stored : p.calRet.current.world.cells.cell binding.before.current.world.cells.size = some binding.raw.asValue
  matching : Matches p.calRet.current.world.receiving binding.raw
  viewBound : binding.raw.view < p.raw.views.length
  cells : List (Option (Received Nat))
  vector : p.calRet.current.world.cells = vectorStore cells
  value : OriginalCalleeDelayProvenance.RuntimeValue
  valueFound : (vectorStore (p.raw.values.map some)).cell binding.raw.value = some value

variable (caller : BoundCaller p)

def BoundCaller.capture : OriginalIdentityCarrier.CaptureAt p.delay p.event :=
  capture_from_bound_caller p caller.binding.before caller.binding.parent caller.binding.raw caller.binding.node caller.binding.found
    caller.binding.descriptor caller.binding.fields caller.saved caller.environments caller.stored caller.matching caller.viewBound

theorem caller_capture_bounds :
    caller.capture.address < p.event.current.world.cells.size ∧
    caller.capture.raw.view < p.event.current.world.receiving.views.size ∧
    caller.capture.raw.value < p.allocation.before.length ∧
    p.delay.environment < p.event.current.world.environments.size := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(preparation_keeps_capture_data p).2.1, caller.vector]
    exact vector_some_bound caller.cells _ _ (caller.vector ▸ caller.stored)
  · change caller.binding.raw.view < _
    have size := (OriginalCalleeDelayProvenance.prepared_view p.raw p.apply.call.site
      p.apply.argumentLabel p.caller p.data).2.1
    change caller.binding.raw.view < (OriginalCalleeDelayProvenance.project p.post).world.receiving.views.size
    rw [show (OriginalCalleeDelayProvenance.project p.post).world.receiving.views.size =
      p.raw.views.length + 1 from size]
    exact Nat.lt_succ_of_lt caller.viewBound
  · have bounded := vector_some_bound (p.raw.values.map some) caller.binding.raw.value caller.value caller.valueFound
    change caller.binding.raw.value < p.allocation.before.length
    simpa only [Preparation.allocation, List.length_map, List.length_range, vectorStore] using bounded
  · exact saved_environment_bound p caller.binding.before caller.binding.parent caller.binding.raw caller.binding.node caller.binding.found
      caller.binding.descriptor caller.binding.fields caller.saved caller.environments

/-- Actual Name evaluation of the freshly allocated Delay. Native binding,
lookup, cell bounds and view match are derived, never a successful-Force input.
Dictionary-enabled dispatch keeps its separate raw-result obligation. -/
theorem caller_name_evaluate :
    OriginalNameForceExtraction.evaluate OriginalNameForceExtraction.noDictionaries p.delay p.event.current.world =
      .ok (caller.capture.address, caller.binding.raw.asValue.atName caller.binding.raw.dispatch) := by
  exact OriginalNameForceExtraction.initialized_evaluate OriginalNameForceExtraction.noDictionaries
    p.delay p.event.current.world caller.capture.address caller.capture.raw caller.binding.raw.dispatch
    caller.capture.lookup (caller_capture_bounds p caller).1 caller.capture.stored rfl
    (caller_capture_bounds p caller).2.1 caller.capture.matching

/-- Readback for every completed finite prefix of this constructor. The graph
also retains zero/open/error prefixes globally. No raw Return/Force is assumed. -/
theorem caller_force_return
    (base : Inputs (S b C Rest Body View))
    (native : OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
      OriginalCalleeDelayProvenance.Metadata Rest Body View)
    (interface : b.Interface)
    (handle : native.handle (p.row interface).input.carrier = some p.delay.handle)
    (snapshot : native.executables p.event = delaySnapshot p.post)
    (mode : OriginalNameForceExtraction.NameMode)
    (modeFound : native.nameMode p.event p.delay.handle = some mode)
    (lexical : mode.lexicalObserve = true)
    (plain : native.dispatch = OriginalNameForceExtraction.noDictionaries) (n : Nat) :
    let observed := OriginalNameForceExtraction.observe native (p.row interface).input p.event p.delay (n + 2)
    (OriginalNameForceExtraction.inputs base native).force (p.row interface).input p.event observed ∧
    (OriginalNameForceExtraction.inputs base native).traceForm (observed.atInterface interface) =
      .pureReturn ⟨caller.capture.descriptor, p.event.eta.views.value caller.binding.raw.value,
        p.event.eta.views.root caller.binding.raw.value, observed.event⟩ ∧
    observed.event.current.world.receiving.receipts.cell p.event.current.world.receiving.receipts.size =
      some ⟨p.event.current.world.control.current, caller.binding.raw.view, p.nameSite, none⟩ := by
  dsimp only
  have owned := prepared_owner p native interface handle snapshot mode modeFound lexical
  refine ⟨OriginalNameForceExtraction.every_owned_prefix base native _ _ _ (n + 2) owned, ?_, ?_⟩
  · rw [OriginalNameForceExtraction.prefix_form base native _ interface p.delay p.event
      caller.capture caller.binding.raw.dispatch (caller_capture_bounds p caller).1
      (by rw [plain]; rfl) (caller_capture_bounds p caller).2.1 (n + 2)]
    simp only [OriginalNameForceExtraction.run, plain, caller_name_evaluate p caller,
      OriginalNameForceExtraction.finish, OriginalNameForceExtraction.Phase.result,
      OriginalIdentityCarrier.resultForm]
    rfl
  · exact (OriginalNameForceExtraction.return_receipt native p.delay p.event caller.capture caller.binding.raw.dispatch
      (caller_capture_bounds p caller).1 (by rw [plain]; rfl)
      (caller_capture_bounds p caller).2.1 n).1


/-- Exactly the remaining surrounding-world/license/future obligations. No
instance is asserted. Allocation, capture, old-value/environment bounds and
fresh carrier/root identity are absent: those were constructed above.
Quantification is ALL original Reach events, including unrelated lawful futures. -/
structure Surrounding (operator : Inputs (S b C Rest Body View))
    (references : Body → Nat → Option Name) (interface : b.Interface) where
  worlds : ∀ event, OriginalIdentityCarrier.Reach operator p.event event →
    Meaning (OriginalParameterSemantics.inputs operator references) (.world event)
  environments : ∀ event, OriginalIdentityCarrier.Reach operator p.event event →
    Extends p.event.current.world.environments event.current.world.environments
  stored : ∀ event, OriginalIdentityCarrier.Reach operator p.event event →
    event.current.world.cells.cell caller.capture.address = some caller.capture.raw
  matchingViews : ∀ event, OriginalIdentityCarrier.Reach operator p.event event →
    Matches event.current.world.receiving caller.capture.raw
  views : ∀ event, OriginalIdentityCarrier.Reach operator p.event event → event.eta.views = p.event.eta.views
  inert : ∀ event, OriginalIdentityCarrier.Reach operator p.event event →
    (operator.carrierGuards ((p.row interface).atEvent event)).Valid
  captures : ∀ event, OriginalIdentityCarrier.Reach operator p.event event →
    OriginalIdentityCarrier.WorldFields (OriginalParameterSemantics.inputs operator references)
      event (operator.carrierCaptures ((p.row interface).atEvent event))
  demand : ∀ event, OriginalIdentityCarrier.Reach operator p.event event → ∀ demand,
    operator.demand ((p.row interface).atEvent event) demand → operator.compatible event demand

/-- Construct the old History with the actual allocation/caller evidence.
This is conditional on the named independent leaves, not a concrete instance
of all-Reach world validity or original reify licensing. -/
def history_from_surrounding (operator : Inputs (S b C Rest Body View))
    (references : Body → Nat → Option Name) (interface : b.Interface)
    (surrounding : Surrounding p caller operator references interface) :
    OriginalIdentityCarrier.History operator references (p.row interface) p.delay where
  allocation := p.allocation
  origin := caller.capture
  existingValue := (caller_capture_bounds p caller).2.2.1
  environmentBound := (caller_capture_bounds p caller).2.2.2
  actualCarrier := rfl
  actualRoot := rfl
  worlds := surrounding.worlds
  environments := surrounding.environments
  stored := surrounding.stored
  matchingViews := surrounding.matchingViews
  views := surrounding.views
  inert := surrounding.inert
  captures := surrounding.captures
  demand := surrounding.demand

/-- Raw native ownership and native-vector projections at one future event.
These do not assert evaluation, trace membership or any source contract.
Their arbitrary-Reach instances are genuine missing native-history leaves. -/
structure NativeRead
    (native : OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
      OriginalCalleeDelayProvenance.Metadata Rest Body View)
    (interface : b.Interface) (event : Event (S b C Rest Body View)) where
  handle : native.handle (p.row interface).input.carrier = some p.delay.handle
  cell : (native.executables event).cell p.delay.handle = some (some p.delay.closure)
  mode : OriginalNameForceExtraction.NameMode
  modeFound : native.nameMode event p.delay.handle = some mode
  lexical : mode.lexicalObserve = true
  cells : List (Option (Received Nat))
  vector : event.current.world.cells = vectorStore cells
  viewBound : caller.capture.raw.view < event.current.world.receiving.views.size

/-- Independent clauses at the COMPUTED native prefix, without its lookup,
result, form, phase-validity or extraction equations. All fuels are retained. -/
structure PrefixFields
    (base : Inputs (S b C Rest Body View))
    (native : OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
      OriginalCalleeDelayProvenance.Metadata Rest Body View)
    (references : Body → Nat → Option Name) (interface : b.Interface)
    (demand : Event (S b C Rest Body View)) where
  compatible : ∀ n, base.compatible demand (OriginalNameForceExtraction.eventAt native p.delay demand n)
  coherent : ∀ n, base.eventCoherent (OriginalNameForceExtraction.eventAt native p.delay demand n)
  worldGuards : ∀ n, (base.worldGuards (OriginalNameForceExtraction.eventAt native p.delay demand n)).Valid
  guards : ∀ n, (base.observationGuards
    ((OriginalNameForceExtraction.observe native (p.row interface).input demand p.delay n).atInterface interface)).Valid
  fields : ∀ n, OriginalIdentityCarrier.WorldFields
    (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
    (OriginalNameForceExtraction.eventAt native p.delay demand n)
    (base.observationFields
      ((OriginalNameForceExtraction.observe native (p.row interface).input demand p.delay n).atInterface interface))

/-- Conditional application of name_delay_whole through the genuine native
extraction constructor. The old History/NativeExtraction/desired carrier Meaning
are constructed, not premises. Every independent missing leaf stays explicit.
There is NO concrete Surrounding/NativeRead/PrefixFields instance here. -/
theorem carrier_from_original_leaves
    (base : Inputs (S b C Rest Body View))
    (native : OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
      OriginalCalleeDelayProvenance.Metadata Rest Body View)
    (references : Body → Nat → Option Name) (interface : b.Interface)
    (plain : native.dispatch = OriginalNameForceExtraction.noDictionaries)
    (surrounding : Surrounding p caller (OriginalNameForceExtraction.inputs base native) references interface)
    (reads : ∀ event, OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event event →
      NativeRead p caller native interface event)
    (prefixes : ∀ event, OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event event →
      ∀ demand, (OriginalNameForceExtraction.inputs base native).demand ((p.row interface).atEvent event) demand →
        PrefixFields p base native references interface demand) :
    Meaning (OriginalParameterSemantics.inputs (OriginalNameForceExtraction.inputs base native) references)
      (.carrier (p.row interface)) := by
  let history := history_from_surrounding p caller (OriginalNameForceExtraction.inputs base native)
    references interface surrounding
  apply OriginalNameForceExtraction.name_delay_from_native_prefixes base native references
    (p.row interface) p.delay history
  · intro event reachable demand demanded
    have later : OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event demand :=
      .later reachable (surrounding.demand event reachable demand demanded)
    let read := reads demand later
    exact owner_from_actual_cell native (p.row interface).input demand p.delay
      read.handle read.cell read.mode read.modeFound read.lexical
  · intro event reachable demand demanded
    have later : OriginalIdentityCarrier.Reach (OriginalNameForceExtraction.inputs base native) p.event demand :=
      .later reachable (surrounding.demand event reachable demand demanded)
    let capture := history.capture demand later
    let read := reads demand later
    let fields := prefixes event reachable demand demanded
    refine ⟨capture.raw.dispatch, ?_, ?_, read.viewBound,
      fields.compatible, fields.coherent, fields.worldGuards, fields.guards, fields.fields⟩
    · rw [read.vector]
      exact vector_some_bound read.cells capture.address capture.raw (read.vector ▸ capture.stored)
    · rw [plain]
      rfl

end NamePreparation
end YulangClosure.OriginalCalleeArgumentHistoryR312
