import YulangClosure.OriginalSourceInterpretation

/-!
Concrete heterogeneous source environments. Runtime event keys contain raw
source operands, never the decorated Event or a source typing certificate.
Independent original field readouts remain explicit data maps where the
selected semantic sorts are opaque. No original challenge is admitted by
looking it up in the stored anchor strategy.
-/
namespace YulangClosure.OriginalSourceEnvironment

open OriginalSource OriginalSourceInterpretation

/-- Raw current execution data. Logical nu/eta, descriptions and proof
witnesses do not occur in this record. -/
structure Current (s : Sorts) where
  history : s.History
  configuration : s.Configuration

inductive Object (s : Sorts) where
  | value (value : s.Value) (root : s.Root)
  | carrier (carrier : s.Carrier) (root : s.Root)

/-- Actual view ownership is a separate token. Its descriptor interpretation
is supplied by the logical environment, not stored in an event identity. -/
structure Invocation (s : Sorts) (View : Type) where
  current : Current s
  value : s.Value
  valueRoot : s.Root
  context : s.Context
  continuation : s.Continuation
  carrier : s.Carrier
  carrierRoot : s.Root
  view : View
  receipt : s.Receipt
  path : s.TypedPath
  consumer : s.Consumer
  incidence : s.Incidence

def Invocation.decorate (raw : Invocation s View) (event : Event s) : Event s :=
  {event with history := raw.current.history, current := raw.current.configuration}

def Invocation.challenge (raw : Invocation s View) (event : Event s)
    (descriptor : s.Descriptor) (viewMeaning : View → s.Interface) :
    Challenge (⟨descriptor, raw.value, raw.valueRoot, raw.decorate event⟩ : ValueRow s) :=
  ⟨raw.context, raw.continuation, raw.carrier, raw.carrierRoot, viewMeaning raw.view,
    raw.receipt, raw.path, raw.consumer, raw.incidence⟩

def encodeInvocation {row : ValueRow s} (challenge : Challenge row) (view : View) :
    Invocation s View :=
  ⟨⟨row.event.history, row.event.current⟩, row.value, row.root, challenge.context, challenge.continuation,
    challenge.carrier, challenge.carrierRoot, view, challenge.receipt,
    challenge.path, challenge.consumer, challenge.incidence⟩

/-- Every original challenge with its genuine view presentation round trips;
the view equation is an original registration fact, not an output-safety test. -/
theorem decode_encode_challenge {row : ValueRow s} (challenge : Challenge row)
    (view : View) (viewMeaning : View → s.Interface)
    (presented : viewMeaning view = challenge.carrierView) :
    (encodeInvocation challenge view).challenge row.event row.descriptor viewMeaning = challenge := by
  cases row
  cases challenge
  simp_all [encodeInvocation, Invocation.challenge, Invocation.decorate]

theorem encode_decode_invocation (raw : Invocation s View) (event : Event s)
    (descriptor : s.Descriptor) (viewMeaning : View → s.Interface) :
    encodeInvocation (raw.challenge event descriptor viewMeaning) raw.view = raw := by
  cases raw
  rfl

/-- Changing only semantic description/event decoration leaves every raw
actual operand and actual view token unchanged. -/
theorem invocation_redecoration (raw : Invocation s View)
    (firstEvent secondEvent : Event s) (first second : s.Descriptor)
    (firstViews secondViews : View → s.Interface) :
    encodeInvocation (raw.challenge firstEvent first firstViews) raw.view =
      encodeInvocation (raw.challenge secondEvent second secondViews) raw.view := by
  rw [encode_decode_invocation, encode_decode_invocation]

structure ReceiptData (s : Sorts) (View : Type) where
  receipt : s.Receipt
  view : View
  path : s.TypedPath
  consumer : s.Consumer
  incidence : s.Incidence
  after : Current s

/-- A source-owned actual suffix can be pending or complete. No eventual
Return or successful typing certificate is required by this data carrier. -/
structure Outcome (s : Sorts) where
  observation : s.Observation
  result : Option (Object s)
  after : Current s
  endpoints : List (Endpoint × Object s)
  bindings : List (Name × Nat)

structure ResponseData (s : Sorts) (View : Type) where
  observation : s.Observation
  receipt : ReceiptData s View

structure RigidData (s : Sorts) where
  declaration : Declaration
  arity : Nat
  packet : s.Observation
  after : Current s

inductive Runtime (s : Sorts) (View : Type) where
  | invocation (data : Invocation s View)
  | receipt (data : ReceiptData s View)
  | returnRebind (data : Outcome s)
  | response (data : ResponseData s View)
  | rigidOperation (data : RigidData s)
  | oneShot (data : Outcome s)

def Runtime.kind : Runtime s View → BinderKind
  | .invocation _ => .invocation
  | .receipt _ => .receipt
  | .returnRebind _ => .returnRebind
  | .response _ => .response
  | .rigidOperation _ => .rigidOperation
  | .oneShot _ => .oneShot

def Runtime.after : Runtime s View → Option (Current s)
  | .invocation data => some data.current
  | .receipt data => some data.after
  | .returnRebind data | .oneShot data => some data.after
  | .response data => some data.receipt.after
  | .rigidOperation data => some data.after

def Runtime.endpoints : Runtime s View → List (Endpoint × Object s)
  | .returnRebind data | .oneShot data => data.endpoints
  | _ => []

def Runtime.bindings : Runtime s View → List (Name × Nat)
  | .returnRebind data | .oneShot data => data.bindings
  | _ => []

/-- Static source-owned callable incidence. An App checks the returned
callee value, whereas a Lambda opens its own closure. Neither endpoint is a
checked descriptor or the App result. -/
inductive CallOwner where
  | application (site : Site) (context : Context) (callee argument : Site)
  | closure (site : Site) (context : Context) (formal pattern body : Site)
  deriving DecidableEq, Repr

def CallOwner.site : CallOwner → Site
  | .application site _ _ _ | .closure site _ _ _ _ => site

def CallOwner.context : CallOwner → Context
  | .application _ context _ _ | .closure _ context _ _ _ => context

def CallOwner.subject : CallOwner → Endpoint
  | .application _ _ callee _ => ⟨callee, .returnedValue⟩
  | .closure site _ _ _ _ => ⟨site, .finalRoot⟩

def CallOwner.initialGoal : CallOwner → Option CheckGoal
  | .application site context callee _ =>
      some ⟨.value, site, context, ⟨callee, .returnedValue⟩, ⟨site, .descriptor⟩⟩
  | .closure _ _ _ _ _ => none

/-- Read only original local source incidence atoms. No solved type, runtime
observation, admission or successful judgment participates in registration. -/
def localCallOwner (rule : Rule) (site : Site) (context : Context)
    (premises : List Premise) : Option CallOwner :=
  premises.findSome? fun premise => match rule, premise with
    | .app, .atom data =>
        if data.kind = .sourceCallIncidence then
          match data.operands with
          | [callee, argument] => some (.application site context callee argument)
          | _ => none
        else none
    | .lambda, .atom data =>
        if data.kind = .closureFormation then
          match data.operands with
          | [formal, pattern, body] => some (.closure site context formal pattern body)
          | _ => none
        else none
    | _, _ => none

mutual
def callOwners : RuleTree → List CallOwner
  | .rule rule site context premises children =>
      (localCallOwner rule site context premises).toList ++ forestCallOwners children
  | .existsE _ body | .forallE _ body | .initializerE _ body | .executionE _ body
  | .sharedE _ body | .publishGroup _ body | .atPublication _ body
  | .aliasPublication _ _ body => callOwners body
  | .choice _ left right => callOwners left ++ callOwners right

def forestCallOwners : RuleForest → List CallOwner
  | .nil => []
  | .cons first rest => callOwners first ++ forestCallOwners rest
end

/-- Every supported raw source constructor is traversed by the immutable
accepted source builder; registration does not require a supplied rule tree. -/
def sourceCallOwners (context : Context) (source : Source category) : List CallOwner :=
  callOwners (sourceRules context source)

theorem source_app_call_owner (context : Context) (site : Site)
    (callee argument : Source .expression) :
    sourceCallOwners context (.app ⟨site, none⟩ callee argument) =
      .application site context callee.site argument.site ::
        (sourceCallOwners context callee ++ sourceCallOwners context argument) := by
  simp only [sourceCallOwners, sourceRules]
  change CallOwner.application site context callee.site argument.site ::
      (sourceCallOwners context callee ++ (sourceCallOwners context argument ++ [])) = _
  simp only [List.append_nil, sourceCallOwners]

/-- This is the actual value premise generated by the App source rule.
Its lower port supplies a callable; its upper port supplies a descriptor. -/
theorem source_app_value_incidence (context : Context) (site : Site)
    (callee argument : Source .expression) :
    ∃ premises children,
      sourceRules context (.app ⟨site, none⟩ callee argument) =
        .existsE ⟨site, .viewLogic, 0⟩ (.rule .app site context premises children) ∧
      Premise.checking ⟨.value, site, context, ⟨callee.site, .returnedValue⟩,
        ⟨site, .descriptor⟩⟩ ∈ premises := by
  simp only [sourceRules]
  let atomPremises := ([AtomKind.descriptorFormation, .wholeArgumentCompatibility,
    .completeCallCertificate, .sourceCallIncidence, .callableImage] ++
    if singletonFormalCall context callee argument then [AtomKind.roleAndInitialCallOrigin] else []).map
      (fun kind => Premise.atom (atom kind site context [callee.site, argument.site]))
  let valueGoal : CheckGoal :=
    ⟨.value, site, context, ⟨callee.site, .returnedValue⟩, ⟨site, .descriptor⟩⟩
  let computationGoal : CheckGoal :=
    ⟨.computation, site, context, ⟨site, .callableImage⟩, ⟨site, .synthesis⟩⟩
  refine ⟨atomPremises ++ [.checking valueGoal, .checking computationGoal],
    .two (sourceRules context callee) (sourceRules context argument), ?_, ?_⟩
  · rfl
  · exact List.mem_append_right _ (List.mem_cons_self)

theorem source_lambda_call_owner (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    (sourceCallOwners context (.lambda ⟨site, none⟩ formal pattern body)).head? =
      some (CallOwner.closure site context formal.site pattern.site body.site) := by
  simp only [sourceCallOwners, sourceRules]
  rfl

structure Root (s : Sorts) (View : Type) where
  assignment : SourceAssignment s
  interfaces : Endpoint → s.Interface
  carriers : Endpoint → s.Carrier
  viewMeaning : View → s.Interface
  installed : Nat → Option (Installed s)
  callOwners : List CallOwner

/-- Descriptor/evidence data has its own non-event frame. Actual endpoint
objects, current configuration and actual view tokens cannot be overwritten. -/
structure Logical (s : Sorts) (View : Type) where
  descriptors : List (Endpoint × s.Descriptor)
  interfaces : List (Endpoint × s.Interface)
  viewMeaning : View → s.Interface
  eta : s.Assignment
  witness : s.JointWitness

inductive LogicalKind where
  | description | viewLogic | publishedInstance | eventProof
  deriving DecidableEq

def LogicalKind.binderKind : LogicalKind → BinderKind
  | .description => .description
  | .viewLogic => .viewLogic
  | .publishedInstance => .publishedInstance
  | .eventProof => .eventProof

structure Shared (s : Sorts) where
  bindings : List (Name × Nat)
  installed : List (Nat × Installed s)
  witness : s.WitnessValue

inductive Payload (s : Sorts) (View : Type) where
  | root (data : Root s View)
  | logical (kind : LogicalKind) (data : Logical s View)
  | shared (data : Shared s)
  | runtime (data : Runtime s View)

def Payload.atKind : Payload s View → BinderKind → Prop
  | .root _, _ => False
  | .logical kind _, binder => kind.binderKind = binder
  | .shared _, binder => binder = .shared
  | .runtime data, binder => data.kind = binder

/-- These opaque original semantic fields need their actual data readout.
There is no Prop, family membership, body-safety or source-typing field.
The result never enters Runtime, EventStep.data or an AnchorKey. -/
structure RuntimeReadout (s : Sorts) (View : Type) where
  eta : List (Frame (Payload s View)) → Event s → Binder → Runtime s View → s.Assignment
  witness : List (Frame (Payload s View)) → Event s → Binder → Runtime s View → s.JointWitness
  scope : List (Frame (Payload s View)) → Event s → Binder → Runtime s View → s.Scope
  authority : List (Frame (Payload s View)) → Event s → Binder → Runtime s View → s.Authority
  incidence : List (Frame (Payload s View)) → Event s → Binder → Runtime s View → s.Incidence
  dictionary : List (Frame (Payload s View)) → Event s → Binder → Runtime s View → s.Dictionary

def RuntimeReadout.event (readout : RuntimeReadout s View)
    (fixedFrames : List (Frame (Payload s View))) (before : Event s)
    (binder : Binder) (data : Runtime s View) : Event s :=
  let after := data.after.getD ⟨before.history, before.current⟩
  {before with
    eta := readout.eta fixedFrames before binder data
    history := after.history
    current := after.configuration
    witness := readout.witness fixedFrames before binder data
    scope := readout.scope fixedFrames before binder data
    authority := readout.authority fixedFrames before binder data
    incidence := readout.incidence fixedFrames before binder data
    dictionary := readout.dictionary fixedFrames before binder data}

structure Decoded (s : Sorts) (View : Type) where
  assignment : SourceAssignment s
  interfaces : Endpoint → s.Interface
  carriers : Endpoint → s.Carrier
  viewMeaning : View → s.Interface
  installed : Nat → Option (Installed s)
  active : Option (CallInput s)
  activeRaw : Option (Invocation s View)
  fixedFrames : List (Frame (Payload s View))
  callOwners : List CallOwner

def Root.decoded (root : Root s View) : Decoded s View :=
  ⟨root.assignment, root.interfaces, root.carriers, root.viewMeaning, root.installed, none, none, [], root.callOwners⟩

/-- Install the canonical source-derived static registry. Logical frames
and actual execution never rewrite this source-owned incidence. -/
def Root.withSource (root : Root s View) (context : Context)
    (source : Source category) : Root s View :=
  {root with callOwners := sourceCallOwners context source}

def Decoded.callOwner (state : Decoded s View) (binder : Binder) : Option CallOwner :=
  state.callOwners.find? (fun owner => owner.site == binder.site)

/-- Total readout for provisional environments. FunctionShape requires the
registered owner, so its semantic application never uses the absent-owner
fallback. The fallback grants no original source incidence. -/
def Decoded.callSubject (state : Decoded s View) (binder : Binder) : Endpoint :=
  ((state.callOwner binder).map CallOwner.subject).getD ⟨binder.site, .finalRoot⟩

def put [DecidableEq Key] (base : Key → Value) (entries : List (Key × Value)) : Key → Value :=
  entries.foldl (fun values entry key => if key = entry.1 then entry.2 else values key) base

theorem put_nil [DecidableEq Key] (base : Key → Value) : put base [] = base := rfl

theorem put_append [DecidableEq Key] (base : Key → Value)
    (first second : List (Key × Value)) : put base (first ++ second) = put (put base first) second := by
  exact List.foldl_append

def Decoded.logical (state : Decoded s View) (data : Logical s View) : Decoded s View :=
  {state with
    assignment := {state.assignment with
      descriptor := put state.assignment.descriptor data.descriptors
      event := {state.assignment.event with eta := data.eta, witness := data.witness}}
    interfaces := put state.interfaces data.interfaces
    viewMeaning := data.viewMeaning}

def Decoded.shared (state : Decoded s View) (data : Shared s) : Decoded s View :=
  {state with
    assignment := {state.assignment with
      binding := put state.assignment.binding (data.bindings.map fun pair => (pair.1, some pair.2))}
    installed := put state.installed (data.installed.map fun pair => (pair.1, some pair.2))}

def Decoded.object (state : Decoded s View) (entry : Endpoint × Object s) : Decoded s View :=
  match entry.2 with
  | .value value root => {state with assignment := {state.assignment with
      value := put state.assignment.value [(entry.1, value)]
      root := put state.assignment.root [(entry.1, root)]}}
  | .carrier carrier root => {state with
      carriers := put state.carriers [(entry.1, carrier)]
      assignment := {state.assignment with root := put state.assignment.root [(entry.1, root)]}}

def Decoded.runtime (readout : RuntimeReadout s View) (state : Decoded s View)
    (binder : Binder) (data : Runtime s View) : Decoded s View :=
  let before := state.assignment.event
  let event := readout.event state.fixedFrames before binder data
  let updated := data.endpoints.foldl Decoded.object state
  {updated with
    assignment := {updated.assignment with
      event := event
      binding := put updated.assignment.binding (data.bindings.map fun pair => (pair.1, some pair.2))}
    active := match data with
      | .invocation call => some ((call.challenge event (state.assignment.descriptor ⟨binder.site, .descriptor⟩)
          state.viewMeaning).input)
      | _ => state.active
    activeRaw := match data with
      | .invocation call => some call
      | _ => state.activeRaw}

def Decoded.retain (state : Decoded s View) (frame : Frame (Payload s View)) : Decoded s View :=
  {state with fixedFrames := state.fixedFrames ++ [frame]}

def decodeFrame (readout : RuntimeReadout s View) (state : Decoded s View)
    (frame : Frame (Payload s View)) : Decoded s View :=
  match frame.value.data with
  | .root _ => state
  | .logical _ data => state.logical data
  | .shared data => (state.shared data).retain frame
  | .runtime data => (state.runtime readout frame.binder data).retain frame

def decode (readout : RuntimeReadout s View) (environment : Environment (Payload s View)) :
    Option (Decoded s View) :=
  match environment.root with
  | .root root => some (environment.frames.foldl (decodeFrame readout) root.decoded)
  | _ => none

theorem decode_extend (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (candidate : ScopedValue (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) :
    decode readout (environment.extend binder candidate) =
      some (decodeFrame readout state ⟨binder, candidate, environment.eventPath⟩) := by
  cases root : environment.root <;> simp only [decode, root, reduceCtorEq] at decoded
  case root rootData =>
    have same := Option.some.inj decoded
    simp only [decode, Environment.extend, root, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact congrArg some (congrArg (fun value => decodeFrame readout value _) same)

theorem logical_preserves_actual_fields (state : Decoded s View) (data : Logical s View) :
    (state.logical data).assignment.value = state.assignment.value ∧
    (state.logical data).assignment.root = state.assignment.root ∧
    (state.logical data).assignment.binding = state.assignment.binding ∧
    (state.logical data).assignment.event.current = state.assignment.event.current ∧
    (state.logical data).assignment.event.history = state.assignment.event.history ∧
    (state.logical data).installed = state.installed ∧
    (state.logical data).active = state.active := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem runtime_preserves_original_fiber (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    (state.runtime readout binder data).assignment.event.fiber = state.assignment.event.fiber ∧
    (state.runtime readout binder data).assignment.event.eta0 = state.assignment.event.eta0 :=
  ⟨rfl, rfl⟩

theorem runtime_invocation_captures_input (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (raw : Invocation s View) :
    (state.runtime readout binder (.invocation raw)).active =
      some ((raw.challenge (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
        (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input) := rfl

/-- A later actual invocation supplies its own current world/history even
when source replay restored a closure's earlier creation prefix. -/
theorem invocation_uses_incoming_current (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (raw : Invocation s View) :
    (state.runtime readout binder (.invocation raw)).assignment.event.current = raw.current.configuration ∧
    (state.runtime readout binder (.invocation raw)).assignment.event.history = raw.current.history :=
  ⟨rfl, rfl⟩

theorem runtime_preserves_call_owners (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    (state.runtime readout binder data).callOwners = state.callOwners := by
  change (data.endpoints.foldl Decoded.object state).callOwners = state.callOwners
  generalize data.endpoints = entries
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons, ih]
      rcases entry with ⟨endpoint, object⟩
      cases object <;> rfl

/-- The complete ordered fold retains the source registry through logical,
Shared and every actual runtime field. It is independent of descriptions. -/
theorem decoded_call_owners (readout : RuntimeReadout s View) (state : Decoded s View)
    (frames : List (Frame (Payload s View))) :
    (frames.foldl (decodeFrame readout) state).callOwners = state.callOwners := by
  induction frames generalizing state with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.foldl_cons, ih]
      cases payload : frame.value.data with
      | root data => simp only [decodeFrame, payload]
      | logical kind data => simp only [decodeFrame, payload, Decoded.logical]
      | shared data => simp only [decodeFrame, payload, Decoded.retain, Decoded.shared]
      | runtime data =>
          simp only [decodeFrame, payload, Decoded.retain, runtime_preserves_call_owners]

theorem logical_kind_is_not_event (kind : LogicalKind) (site : Site) (arity : Nat) :
    (⟨site, kind.binderKind, arity⟩ : Binder).isEvent = false := by
  cases kind <;> rfl

theorem runtime_kind_is_event (data : Runtime s View) (site : Site) (arity : Nat) :
    (⟨site, data.kind, arity⟩ : Binder).isEvent = true := by
  cases data <;> rfl

/-- The description-owned value is absent from the actual event path. This
holds for all logical assignments/readouts, not only one chosen strategy. -/
theorem logical_extension_keeps_actual_path
    (environment : Environment (Payload s View)) (kind : LogicalKind)
    (site : Site) (arity : Nat) (data : Logical s View)
    (event : ActualEvent (Payload s View)) :
    (environment.extend ⟨site, kind.binderKind, arity⟩ ⟨.logical kind data, event⟩).eventPath =
      environment.eventPath := by
  simp only [Environment.extend, logical_kind_is_not_event, Bool.false_eq_true, ite_false]

theorem logical_extension_keeps_anchor
    (environment : Environment (Payload s View)) (kind : LogicalKind)
    (site : Site) (arity : Nat) (data : Logical s View)
    (event : ActualEvent (Payload s View)) (owned : Binder) :
    (environment.extend ⟨site, kind.binderKind, arity⟩ ⟨.logical kind data, event⟩).anchorValue owned =
      environment.anchorValue owned := by
  simp only [Environment.anchorValue, Environment.anchorKey, Environment.extend,
    logical_kind_is_not_event, Bool.false_eq_true, ite_false]

theorem actual_runtime_path (environment : Environment (Payload s View))
    (site : Site) (arity : Nat) (data : Runtime s View)
    (event : ActualEvent (Payload s View)) :
    (environment.extend ⟨site, data.kind, arity⟩ ⟨.runtime data, event⟩).eventPath =
      environment.eventPath ++ [⟨site, data.kind, event.occurrence, .runtime data⟩] := by
  simp only [Environment.extend, runtime_kind_is_event, ite_true, ActualEvent.path]

/-- The same actual event under two independent descriptions has the same
raw key, even when their complete logical view interpretations differ. -/
theorem two_descriptions_one_runtime_key
    (environment : Environment (Payload s View)) (kind : LogicalKind)
    (descriptionSite : Site) (first second : Logical s View)
    (descriptionEvent event : ActualEvent (Payload s View))
    (site : Site) (arity : Nat) (data : Runtime s View) (next : Binder) :
    (((environment.extend ⟨descriptionSite, kind.binderKind, 0⟩ ⟨.logical kind first, descriptionEvent⟩).extend ⟨site, data.kind, arity⟩ ⟨.runtime data, event⟩).anchorKey next) =
    (((environment.extend ⟨descriptionSite, kind.binderKind, 0⟩ ⟨.logical kind second, descriptionEvent⟩).extend ⟨site, data.kind, arity⟩ ⟨.runtime data, event⟩).anchorKey next) := by
  simp only [Environment.anchorKey, Environment.extend, logical_kind_is_not_event,
    runtime_kind_is_event, Bool.false_eq_true, ite_false, ite_true, ActualEvent.path]

/-- Raw payload differences at the same source occurrence remain observable
in actual event identity; no anchor strategy substitutes another payload. -/
theorem distinct_runtime_payloads (environment : Environment (Payload s View))
    (site : Site) (arity occurrence : Nat) (first second : Runtime s View)
    (different : first ≠ second) :
    (environment.extend ⟨site, first.kind, arity⟩
      ⟨.runtime first, ⟨environment.eventPath, occurrence⟩⟩).eventPath ≠
    (environment.extend ⟨site, second.kind, arity⟩
      ⟨.runtime second, ⟨environment.eventPath, occurrence⟩⟩).eventPath := by
  rw [actual_runtime_path, actual_runtime_path]
  intro same
  have rows := List.append_cancel_left same
  have entry := List.cons.inj rows
  have payload := congrArg EventStep.data entry.1
  exact different (Payload.runtime.inj payload)

def Decoded.callRow (state : Decoded s View) (binder : Binder) : ValueRow s :=
  ⟨state.assignment.descriptor ⟨binder.site, .descriptor⟩,
    state.assignment.value (state.callSubject binder),
    state.assignment.root (state.callSubject binder), state.assignment.event⟩

/-- Intermediate descriptor comparisons retain the same actual callable
subject; only the checked upper descriptor changes. -/
def Decoded.goalRow (state : Decoded s View) (binder : Binder) (goal : CheckGoal) : ValueRow s :=
  (state.callRow binder).withDescriptor (state.assignment.descriptor goal.upper)

theorem goal_row_same_subject (state : Decoded s View) (binder : Binder)
    (first second : CheckGoal) :
    (state.goalRow binder first).value = (state.goalRow binder second).value ∧
    (state.goalRow binder first).root = (state.goalRow binder second).root ∧
    (state.goalRow binder first).event = (state.goalRow binder second).event := ⟨rfl, rfl, rfl⟩

theorem logical_preserves_callable_owner (state : Decoded s View) (data : Logical s View)
    (binder : Binder) :
    (state.logical data).callOwner binder = state.callOwner binder ∧
    (state.logical data).callSubject binder = state.callSubject binder ∧
    ((state.logical data).callRow binder).value = (state.callRow binder).value ∧
    ((state.logical data).callRow binder).root = (state.callRow binder).root := ⟨rfl, rfl, rfl, rfl⟩

theorem registered_app_subject (root : Root s View) (context : Context) (site : Site)
    (callee argument : Source .expression) :
    ((root.withSource context (.app ⟨site, none⟩ callee argument)).decoded.callSubject
      ⟨site, .invocation, 0⟩) = ⟨callee.site, .returnedValue⟩ := by
  simp [Root.withSource, Root.decoded, Decoded.callSubject, Decoded.callOwner,
    source_app_call_owner, CallOwner.site, CallOwner.subject]

theorem registered_lambda_subject (root : Root s View) (context : Context) (site : Site)
    (formal : Formal) (pattern : Source .pattern) (body : Source .expression) :
    ((root.withSource context (.lambda ⟨site, none⟩ formal pattern body)).decoded.callSubject
      ⟨site, .invocation, 0⟩) = ⟨site, .finalRoot⟩ := by
  have head := source_lambda_call_owner context site formal pattern body
  cases owners : sourceCallOwners context (.lambda ⟨site, none⟩ formal pattern body) with
  | nil => simp [owners] at head
  | cons first rest =>
      have firstOwner : first = .closure site context formal.site pattern.site body.site :=
        Option.some.inj (by simpa only [owners, List.head?_cons] using head)
      subst first
      simp [Root.withSource, Root.decoded, Decoded.callSubject, Decoded.callOwner,
        owners, CallOwner.site, CallOwner.subject]

theorem registered_app_callable (root : Root s View) (context : Context) (site : Site)
    (callee argument : Source .expression) :
    let state := (root.withSource context (.app ⟨site, none⟩ callee argument)).decoded
    (state.callRow ⟨site, .invocation, 0⟩).value = root.assignment.value ⟨callee.site, .returnedValue⟩ ∧
    (state.callRow ⟨site, .invocation, 0⟩).root = root.assignment.root ⟨callee.site, .returnedValue⟩ := by
  dsimp only
  simp only [Decoded.callRow, registered_app_subject]
  exact ⟨rfl, rfl⟩

theorem registered_lambda_callable (root : Root s View) (context : Context) (site : Site)
    (formal : Formal) (pattern : Source .pattern) (body : Source .expression) :
    let state := (root.withSource context (.lambda ⟨site, none⟩ formal pattern body)).decoded
    (state.callRow ⟨site, .invocation, 0⟩).value = root.assignment.value ⟨site, .finalRoot⟩ ∧
    (state.callRow ⟨site, .invocation, 0⟩).root = root.assignment.root ⟨site, .finalRoot⟩ := by
  dsimp only
  simp only [Decoded.callRow, registered_lambda_subject]
  exact ⟨rfl, rfl⟩

/-- All other owning-rule admissions are independent local input relations.
They are separated by actual source field class. No Function/body success or
recursive semantic family occurs in this interface. -/
structure LocalAdmissions (s : Sorts) (View : Type) where
  logical : Decoded s View → Binder → LogicalKind → Logical s View → Prop
  shared : Decoded s View → Binder → Shared s → Prop
  receipt : Decoded s View → Binder → ReceiptData s View → Prop
  returnRebind : Decoded s View → Binder → Outcome s → Prop
  response : Decoded s View → Binder → ResponseData s View → Prop
  rigidOperation : Decoded s View → Binder → RigidData s → Prop
  oneShot : Decoded s View → Binder → Outcome s → Prop

def DataAdmitted (inputs : Inputs s) (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (state : Decoded s View) (binder : Binder) : Payload s View → Prop
  | .root _ => False
  | .logical kind data => kind.binderKind = binder.kind ∧ admissions.logical state binder kind data
  | .shared data => binder.kind = .shared ∧ admissions.shared state binder data
  | .runtime (.invocation raw) =>
      binder.kind = .invocation ∧ raw.value = (state.callRow binder).value ∧
      raw.valueRoot = (state.callRow binder).root ∧
      CheckedDomain inputs (raw.challenge (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
        (state.callRow binder).descriptor state.viewMeaning)
  | .runtime (.receipt data) => binder.kind = .receipt ∧ admissions.receipt state binder data
  | .runtime (.returnRebind data) => binder.kind = .returnRebind ∧ admissions.returnRebind state binder data
  | .runtime (.response data) => binder.kind = .response ∧ admissions.response state binder data
  | .runtime (.rigidOperation data) => binder.kind = .rigidOperation ∧ admissions.rigidOperation state binder data
  | .runtime (.oneShot data) => binder.kind = .oneShot ∧ admissions.oneShot state binder data

/-- Admission and observation capture use one actual source subject. The
checked descriptor and the eventual App result are not consulted for identity. -/
theorem admitted_invocation_captures_subject (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (state : Decoded s View) (binder : Binder) (raw : Invocation s View)
    (admitted : DataAdmitted inputs readout admissions state binder (.runtime (.invocation raw))) :
    ((state.runtime readout binder (.invocation raw)).active.map
      (fun input => (input.value, input.valueRoot))) =
        some (state.assignment.value (state.callSubject binder),
          state.assignment.root (state.callSubject binder)) := by
  change some (raw.value, raw.valueRoot) = _
  rw [admitted.2.1, admitted.2.2.1]
  rfl

def Admitted (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (binder : Binder) (candidate : ScopedValue (Payload s View)) : Prop :=
  candidate.event.parents = environment.eventPath ∧ ∃ state,
    decode readout environment = some state ∧ DataAdmitted inputs readout admissions state binder candidate.data

def scopeCandidate (environment : Environment (Payload s View)) (occurrence : Nat)
    (data : Payload s View) : ScopedValue (Payload s View) :=
  ⟨data, ⟨environment.eventPath, occurrence⟩⟩

theorem admitted_scoped_iff (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (binder : Binder) (state : Decoded s View) (decoded : decode readout environment = some state)
    (occurrence : Nat) (data : Payload s View) :
    Admitted inputs readout admissions environment binder (scopeCandidate environment occurrence data) ↔
      DataAdmitted inputs readout admissions state binder data := by
  simp only [Admitted, scopeCandidate, decoded, Option.some.injEq, true_and]
  constructor
  · rintro ⟨other, equal, valid⟩
    subst other
    exact valid
  · intro valid
    exact ⟨state, rfl, valid⟩

/-- Every complete original admitted challenge is encoded at every actual
occurrence, given only its original view-registration readback. This premise
neither tests safety nor restricts the original domain by definition. -/
theorem original_challenge_supplies_admission (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (invocation : binder.kind = .invocation) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (challenge : Challenge (state.callRow binder)) (admitted : CheckedDomain inputs challenge)
    (view : View) (presented : state.viewMeaning view = challenge.carrierView)
    (readback : readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge view)) =
      (state.callRow binder).event)
    (occurrence : Nat) :
    Admitted inputs readout admissions environment binder
      (scopeCandidate environment occurrence (.runtime (.invocation (encodeInvocation challenge view)))) := by
  apply (admitted_scoped_iff inputs readout admissions environment binder state decoded occurrence _).mpr
  refine ⟨invocation, rfl, rfl, ?_⟩
  rw [readback]
  change CheckedDomain inputs ((encodeInvocation challenge view).challenge
    (state.callRow binder).event (state.callRow binder).descriptor state.viewMeaning)
  rw [decode_encode_challenge challenge view state.viewMeaning presented]
  exact admitted

/-- Kernel admission yields the unchanged complete semantic challenge, with
all raw receipt/path/consumer/incidence fields and its actual callable/root. -/
theorem admission_recovers_challenge (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (binder : Binder) (state : Decoded s View) (decoded : decode readout environment = some state)
    (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions environment binder candidate)
    (invocation : binder.kind = .invocation) :
    ∃ raw : Invocation s View, candidate.data = .runtime (.invocation raw) ∧
      raw.value = (state.callRow binder).value ∧ raw.valueRoot = (state.callRow binder).root ∧
      CheckedDomain inputs (raw.challenge (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
        (state.callRow binder).descriptor state.viewMeaning) := by
  obtain ⟨_, other, decodedOther, valid⟩ := admitted
  have same : other = state := Option.some.inj (decodedOther.symm.trans decoded)
  subst other
  cases payload : candidate.data with
  | root _ => simp only [payload, DataAdmitted] at valid
  | logical kind data =>
      simp only [payload, DataAdmitted, invocation] at valid
      cases kind <;> simp [LogicalKind.binderKind] at valid
  | shared data => simp only [payload, DataAdmitted, invocation, reduceCtorEq, false_and] at valid
  | runtime data =>
      cases data with
      | invocation raw =>
          simp only [payload, DataAdmitted] at valid
          exact ⟨raw, rfl, valid.2.1, valid.2.2.1, valid.2.2.2⟩
      | receipt data | returnRebind data | response data | rigidOperation data | oneShot data =>
          simp only [payload, DataAdmitted, invocation, reduceCtorEq, false_and] at valid

/-- Admission is invariant under replacing either stored strategy map.
Neither anchors nor publication lookup is an admission-domain filter. -/
theorem admission_ignores_stored_maps (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (anchors : AnchorKey (Payload s View) → ScopedValue (Payload s View))
    (publications : PublicationId (Payload s View) → Option (PublicationRecord (Payload s View)))
    (binder : Binder) (candidate : ScopedValue (Payload s View)) :
    Admitted inputs readout admissions {environment with anchors := anchors, publications := publications}
      binder candidate ↔ Admitted inputs readout admissions environment binder candidate := Iff.rfl

def admissionKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) : Kernel (Payload s View) :=
  {original with
    admitted := Admitted inputs readout admissions
    checkingAdmitted := fun environment _ binder candidate =>
      Admitted inputs readout admissions environment binder candidate}

/-- The actual native view token is retained independently of its semantic
readout. Other native receipt fields remain in the original receipt object. -/
def nativeReceiptSorts (s : Sorts) (Key SiteData : Type) : Sorts :=
  {s with Receipt := SourceIdentityWorld.Receipt Key SiteData}

def nativeInvocation (template : Invocation (nativeReceiptSorts s Key SiteData) Nat)
    (argument : SourceIdentityWorld.Received s.Carrier)
    (receipt : SourceIdentityWorld.Receipt Key SiteData) :
    Invocation (nativeReceiptSorts s Key SiteData) Nat :=
  {template with carrier := argument.value, view := argument.view, receipt := receipt}

theorem native_invocation_retains_receipt
    (template : Invocation (nativeReceiptSorts s Key SiteData) Nat)
    (argument : SourceIdentityWorld.Received s.Carrier)
    (receipt : SourceIdentityWorld.Receipt Key SiteData) :
    (nativeInvocation template argument receipt).view = argument.view ∧
    (nativeInvocation template argument receipt).carrier = argument.value ∧
    (nativeInvocation template argument receipt).receipt = receipt := ⟨rfl, rfl, rfl⟩

/-- Actual receipt construction supplies exactly owner, view, site and formal;
the view is an original allocation token, not a checked Function description. -/
theorem native_receipt_token_owned [DecidableEq Key]
    (receiving : SourceIdentityWorld.Receiving Key Value ViewData SiteData)
    (owner : SourceIdentityWorld.Owner) (view : Nat) (site : SiteData) (formal : Option Key) :
    (receiving.record owner view site formal).receipts.cell receiving.receipts.size =
      some {owner := owner, view := view, site := site, formal := formal} :=
  SourceIdentityWorld.receipt_new receiving owner view site formal

/-- Projection of actual fields from the complete deterministic fold. This
contains no descriptor interpretation of a view and no logical assignment. -/
structure Actual (s : Sorts) (View : Type) where
  current : Current s
  values : Endpoint → s.Value
  roots : Endpoint → s.Root
  carriers : Endpoint → s.Carrier
  bindings : Name → Option Nat
  installed : Nat → Option (Installed s)
  active : Option (Invocation s View)
  fixedFrames : List (Frame (Payload s View))
  callOwners : List CallOwner

def Decoded.actual (state : Decoded s View) : Actual s View :=
  ⟨⟨state.assignment.event.history, state.assignment.event.current⟩,
    state.assignment.value, state.assignment.root, state.carriers,
    state.assignment.binding, state.installed, state.activeRaw, state.fixedFrames, state.callOwners⟩

def Actual.object (state : Actual s View) (entry : Endpoint × Object s) : Actual s View :=
  match entry.2 with
  | .value value root => {state with
      values := put state.values [(entry.1, value)]
      roots := put state.roots [(entry.1, root)]}
  | .carrier carrier root => {state with
      carriers := put state.carriers [(entry.1, carrier)]
      roots := put state.roots [(entry.1, root)]}

def Actual.shared (state : Actual s View) (data : Shared s) : Actual s View :=
  {state with
    bindings := put state.bindings (data.bindings.map fun pair => (pair.1, some pair.2))
    installed := put state.installed (data.installed.map fun pair => (pair.1, some pair.2))}

def Actual.runtime (state : Actual s View) (data : Runtime s View) : Actual s View :=
  let updated := data.endpoints.foldl Actual.object state
  {updated with
    current := data.after.getD state.current
    bindings := put updated.bindings (data.bindings.map fun pair => (pair.1, some pair.2))
    active := match data with
      | .invocation raw => some raw
      | _ => state.active}

def Actual.retain (state : Actual s View) (frame : Frame (Payload s View)) : Actual s View :=
  {state with fixedFrames := state.fixedFrames ++ [frame]}

theorem actual_retain (state : Decoded s View) (frame : Frame (Payload s View)) :
    (state.retain frame).actual = state.actual.retain frame := rfl

def actualFrame (state : Actual s View) (frame : Frame (Payload s View)) : Actual s View :=
  match frame.value.data with
  | .root _ | .logical _ _ => state
  | .shared data => (state.shared data).retain frame
  | .runtime data => (state.runtime data).retain frame

theorem actual_logical (state : Decoded s View) (data : Logical s View) :
    (state.logical data).actual = state.actual := rfl

theorem actual_shared (state : Decoded s View) (data : Shared s) :
    (state.shared data).actual = state.actual.shared data := rfl

theorem actual_object (state : Decoded s View) (entry : Endpoint × Object s) :
    (state.object entry).actual = state.actual.object entry := by
  rcases entry with ⟨endpoint, object⟩
  cases object <;> rfl

theorem actual_objects (state : Decoded s View) (entries : List (Endpoint × Object s)) :
    (entries.foldl Decoded.object state).actual = entries.foldl Actual.object state.actual := by
  induction entries generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, actual_object]

theorem actual_runtime (readout : RuntimeReadout s View) (state : Decoded s View)
    (binder : Binder) (data : Runtime s View) :
    (state.runtime readout binder data).actual = state.actual.runtime data := by
  change { (data.endpoints.foldl Decoded.object state).actual with
    current := data.after.getD state.actual.current
    bindings := put (data.endpoints.foldl Decoded.object state).actual.bindings
      (data.bindings.map fun (pair : Name × Nat) => (pair.1, some pair.2))
    active := match data with | .invocation raw => some raw | _ => state.actual.active } = _
  rw [actual_objects]
  rfl

theorem actual_frame (readout : RuntimeReadout s View) (state : Decoded s View)
    (frame : Frame (Payload s View)) :
    (decodeFrame readout state frame).actual = actualFrame state.actual frame := by
  cases payload : frame.value.data with
  | root data => simp only [decodeFrame, actualFrame, payload]
  | logical kind data => simpa only [decodeFrame, actualFrame, payload] using actual_logical state data
  | shared data => simp only [decodeFrame, actualFrame, payload, actual_retain, actual_shared]
  | runtime data => simp only [decodeFrame, actualFrame, payload, actual_retain, actual_runtime]

/-- A complete frame fold has a separately computed raw projection. Thus
changing logical/readout choices cannot retroactively change actual objects,
current configurations, stored cells or active raw invocation data. -/
theorem actual_frames (readout : RuntimeReadout s View) (state : Decoded s View)
    (frames : List (Frame (Payload s View))) :
    (frames.foldl (decodeFrame readout) state).actual = frames.foldl actualFrame state.actual := by
  induction frames generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, actual_frame]

theorem fold_actual_independent_of_readout
    (firstReadout secondReadout : RuntimeReadout s View)
    (first second : Decoded s View) (same : first.actual = second.actual)
    (frames : List (Frame (Payload s View))) :
    (frames.foldl (decodeFrame firstReadout) first).actual =
      (frames.foldl (decodeFrame secondReadout) second).actual := by
  rw [actual_frames, actual_frames, same]

def LogicalFrame (frame : Frame (Payload s View)) : Prop :=
  ∃ kind data, frame.value.data = .logical kind data

theorem logical_frames_preserve_actual (readout : RuntimeReadout s View)
    (state : Decoded s View) (frames : List (Frame (Payload s View)))
    (logical : ∀ frame ∈ frames, LogicalFrame frame) :
    (frames.foldl (decodeFrame readout) state).actual = state.actual := by
  induction frames generalizing state with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨kind, data, payload⟩ := logical first (List.mem_cons_self)
      simp only [List.foldl_cons]
      rw [ih _ (fun frame member => logical frame (List.mem_cons_of_mem _ member))]
      simp only [decodeFrame, payload, actual_logical]

theorem data_admitted_has_original_field_kind (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (state : Decoded s View) (binder : Binder) (data : Payload s View)
    (admitted : DataAdmitted inputs readout admissions state binder data) :
    data.atKind binder.kind := by
  cases data with
  | root data => exact False.elim admitted
  | logical kind data => exact admitted.1
  | shared data => exact admitted.1
  | runtime data =>
      cases data <;> exact admitted.1.symm

theorem nonfixed_typed_frame_is_logical (frame : Frame (Payload s View))
    (typed : frame.value.data.atKind frame.binder.kind)
    (notFixed : frame.binder.isFixed = false) : LogicalFrame frame := by
  cases payload : frame.value.data with
  | root data => simp only [payload, Payload.atKind] at typed
  | logical kind data => exact ⟨kind, data, payload⟩
  | shared data =>
      simp only [payload, Payload.atKind] at typed
      simp [Binder.isFixed, Binder.isEvent, typed] at notFixed
  | runtime data =>
      simp only [payload, Payload.atKind] at typed
      cases data <;> simp only [Runtime.kind] at typed
      all_goals simp [Binder.isFixed, Binder.isEvent, ← typed] at notFixed

def TypedFrames (environment : Environment (Payload s View)) : Prop :=
  ∀ frame ∈ environment.frames, frame.value.data.atKind frame.binder.kind

theorem admission_preserves_typed_frames (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (typed : TypedFrames environment) (binder : Binder) (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions environment binder candidate) :
    TypedFrames (environment.extend binder candidate) := by
  obtain ⟨_, state, _, data⟩ := admitted
  intro frame member
  simp only [Environment.extend, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact typed frame old
  · exact data_admitted_has_original_field_kind inputs readout admissions state binder candidate.data data

theorem decode_initializer_entry (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (site : Site) :
    decode readout (environment.enterInitializer site) = decode readout environment := rfl

/-- Restoration decodes the actual entry prefix, not completed initializer
frames. Remaining caller description frames cannot alter its actual state.
The full completed fixed history remains separately available for replay. -/
theorem restore_decodes_actual_entry (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (root : Root s View)
    (rootData : environment.root = .root root) (typed : TypedFrames environment)
    (record : PublicationRecord (Payload s View)) :
    (decode readout (environment.restore record)).map Decoded.actual =
      some ((record.entryFrames.foldl (decodeFrame readout) root.decoded).actual) := by
  simp only [decode, Environment.restore, rootData, List.foldl_append, Option.map_some]
  apply congrArg some
  apply logical_frames_preserve_actual
  intro frame member
  have info := List.mem_filter.mp member
  apply nonfixed_typed_frame_is_logical frame (typed frame info.1)
  cases fixed : frame.binder.isFixed <;> simp_all

theorem restore_keeps_completed_replay (environment : Environment (Payload s View))
    (record : PublicationRecord (Payload s View)) :
    (environment.restore record).replay = some record.fixedFrames ∧
    (environment.restore record).names = record.entryNames ∧
    (environment.restore record).publications = environment.publications := ⟨rfl, rfl, rfl⟩

theorem decode_alias (readout : RuntimeReadout s View)
    (environment next : Environment (Payload s View)) (original aliasName : Name)
    (aliased : environment.aliasPublication original aliasName = some next) :
    decode readout next = decode readout environment := by
  cases found : environment.publicationName original with
  | none => simp [Environment.aliasPublication, found] at aliased
  | some identity =>
      simp [Environment.aliasPublication, found] at aliased
      subst next
      rfl

/-- Actual local semantic clauses use the entire decoded frame prefix,
rather than silently reading the unchanged Environment.root assignment. -/
def foldedLiteralKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
    (site : Site) (literal : Literal) : Kernel (Payload s View) :=
  {original with atom := fun environment atom =>
    if atom.kind = .literalDeclaration ∧ atom.site = site ∧ atom.literal = some literal then
      ∃ state, decode readout environment = some state ∧ LiteralAtom inputs declarations state.assignment atom
    else original.atom environment atom}

def foldedNameKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (original : Kernel (Payload s View)) (site : Site) (name : Name) : Kernel (Payload s View) :=
  {original with atom := fun environment atom =>
    if atom.site = site ∧ atom.names = [name] ∧
      (atom.kind = .resolvedSameBinding ∨ atom.kind = .computedFetchOnce) ∧ valueFormalAtom atom = true then
      ∃ state, decode readout environment = some state ∧ ValueNameAtom inputs state.assignment atom
    else original.atom environment atom}

theorem folded_generated_literal_membership (inputs : Inputs s) (law : GroundLaw inputs)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (context : Context) (site : Site) (literal : Literal)
    (solved : Satisfies (foldedLiteralKernel inputs readout declarations original site literal) environment
      (Build context (.literal ⟨site, none⟩ literal))) :
    Meaning inputs (.value (state.assignment.row site)) := by
  have derivation := generated_constraints_imply_source_judgment
    (foldedLiteralKernel inputs readout declarations original site literal) environment context
    (.literal ⟨site, none⟩ literal) solved
  simp only [SourceJudgment, sourceRules] at derivation
  cases derivation with
  | rule locals children =>
      have primitive := locals _ (List.mem_cons_self)
      cases primitive with
      | atom valid =>
          simp [foldedLiteralKernel, OriginalSource.atom] at valid
          obtain ⟨other, otherDecoded, _, _, _, form, ground⟩ := valid
          have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
          subst other
          exact ground_membership inputs law _ form ground

theorem folded_name_constraints_from_binding (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (site owner : Site) (name : Name) (address : Nat)
    (binding : state.assignment.binding name = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨site, .finalRoot⟩)
        (state.assignment.value ⟨site, .finalRoot⟩) (state.assignment.root ⟨site, .finalRoot⟩))) :
    Satisfies (foldedNameKernel inputs readout original site name) environment
      (Build (formalContext name owner) (.name ⟨site, none⟩ name)) := by
  apply (source_reconstruction _ _ _ _).mpr
  have lookup : lookupBinding (formalContext name owner) name =
      some {name := name, owner := owner, kind := .formal, entry := some .value} := by
    simp [lookupBinding, formalContext]
  simp only [SourceJudgment, sourceRules, lookup]
  apply Judgment.rule
  · intro premise member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      apply Local.atom
      simp only [foldedNameKernel, OriginalSource.atom, valueFormalAtom]
      simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or, or_true, and_self, ite_true]
      exact ⟨state, decoded, name, address, rfl, binding, bound, found⟩
  · exact .nil

theorem folded_generated_name_membership (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (site owner : Site) (name : Name)
    (world : Meaning inputs (.world state.assignment.event))
    (solved : Satisfies (foldedNameKernel inputs readout original site name) environment
      (Build (formalContext name owner) (.name ⟨site, none⟩ name))) :
    Meaning inputs (.value (state.assignment.row site)) := by
  have derivation := generated_constraints_imply_source_judgment
    (foldedNameKernel inputs readout original site name) environment
    (formalContext name owner) (.name ⟨site, none⟩ name) solved
  have lookup : lookupBinding (formalContext name owner) name =
      some {name := name, owner := owner, kind := .formal, entry := some .value} := by
    simp [lookupBinding, formalContext]
  simp only [SourceJudgment, sourceRules, lookup] at derivation
  cases derivation with
  | rule locals children =>
      have first := locals _ (List.mem_cons_self)
      cases first with
      | atom valid =>
          simp only [foldedNameKernel, OriginalSource.atom, valueFormalAtom] at valid
          simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or, and_self, ite_true] at valid
          obtain ⟨other, otherDecoded, _, address, _, _, _, found⟩ := valid
          have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
          subst other
          exact immutable_name_value inputs state.assignment.event world address _ _ _ found

/-- Exact finite Function-check incidence. These fields identify recursive
domain/observation children and the actual callable; no inclusion or body
certificate is a shape field. -/
structure FunctionShape (inputs : Inputs s) (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (goal domain : CheckGoal)
    (binder : Binder) (observation : CheckGoal) : Prop where
  valueMode : goal.mode = .value
  domainMode : domain.mode = .domain
  observationMode : observation.mode = .observation
  invocationKind : binder.kind = .invocation
  owner : binder.site = goal.site
  domainLower : domain.lower = goal.upper
  domainUpper : domain.upper = goal.lower
  observationLower : observation.lower = goal.lower
  observationUpper : observation.upper = goal.upper
  domainContext : domain.context = goal.context
  observationContext : observation.context = goal.context
  decoded : ∃ state, decode readout environment = some state ∧
    (∃ owner, state.callOwner binder = some owner ∧ owner.site = goal.site ∧
      owner.context = goal.context) ∧
    inputs.valueForm (state.assignment.descriptor goal.lower) = .function ∧
    inputs.valueForm (state.assignment.descriptor goal.upper) = .function

/-- Any lower/middle/upper descriptor endpoints may be used at the same
registered source occurrence. Shape does not assert the separate domain
alignment needed to apply the existing source invocation telescope. -/
theorem function_shape_for_registered_owner (inputs : Inputs s) (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (site : Site) (context : Context)
    (lower upper : Endpoint) (owner : CallOwner)
    (registered : state.callOwner ⟨site, .invocation, 0⟩ = some owner)
    (ownerSite : owner.site = site) (ownerContext : owner.context = context)
    (lowerForm : inputs.valueForm (state.assignment.descriptor lower) = .function)
    (upperForm : inputs.valueForm (state.assignment.descriptor upper) = .function) :
    FunctionShape inputs readout environment ⟨.value, site, context, lower, upper⟩
      ⟨.domain, site, context, upper, lower⟩ ⟨site, .invocation, 0⟩
      ⟨.observation, site, context, lower, upper⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    state, decoded, ⟨owner, registered, ownerSite, ownerContext⟩, lowerForm, upperForm⟩

def functionKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) : Kernel (Payload s View) :=
  {original with
    admitted := Admitted inputs readout admissions
    checkingAdmitted := fun environment _ binder candidate =>
      Admitted inputs readout admissions environment binder candidate
    functionShape := FunctionShape inputs readout}

def inputChallenge (input : CallInput s) (descriptor : s.Descriptor) :
    Challenge (⟨descriptor, input.value, input.valueRoot, input.event⟩ : ValueRow s) :=
  ⟨input.context, input.continuation, input.carrier, input.carrierRoot, input.carrierView,
    input.receipt, input.path, input.consumer, input.incidence⟩

def DomainMeaning (inputs : Inputs s) (state : Decoded s View) (goal : CheckGoal) : Prop :=
  ∀ (value : s.Value) (root : s.Root)
    (challenge : Challenge (⟨state.assignment.descriptor goal.lower, value, root,
      state.assignment.event⟩ : ValueRow s)),
    CheckedDomain inputs challenge →
      CheckedDomain inputs (challenge.retarget (state.assignment.descriptor goal.upper))

def ObservationMeaning (inputs : Inputs s) (Z : Family s) (state : Decoded s View)
    (goal : CheckGoal) : Prop :=
  match state.active with
  | none => False
  | some input => ∀ raw,
      ObservationMem inputs Z (inputChallenge input (state.assignment.descriptor goal.lower)) raw →
        ObservationMem inputs Z (inputChallenge input (state.assignment.descriptor goal.upper)) raw

theorem object_preserves_descriptors (state : Decoded s View) (entry : Endpoint × Object s) :
    (state.object entry).assignment.descriptor = state.assignment.descriptor := by
  rcases entry with ⟨endpoint, object⟩
  cases object <;> rfl

theorem objects_preserve_descriptors (state : Decoded s View) (entries : List (Endpoint × Object s)) :
    (entries.foldl Decoded.object state).assignment.descriptor = state.assignment.descriptor := by
  induction entries generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, object_preserves_descriptors]

theorem runtime_preserves_descriptors (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    (state.runtime readout binder data).assignment.descriptor = state.assignment.descriptor :=
  objects_preserve_descriptors state data.endpoints

theorem challenge_input_readback {row : ValueRow s} (challenge : Challenge row)
    (descriptor : s.Descriptor) :
    inputChallenge challenge.input descriptor = challenge.retarget descriptor := rfl

/-- The actual universally admitted source binder supplies the full
descriptor-indexed P_A[Z] to P_F[Z] transport from its observation child.
View/event readback are data-incidence equations, not domain/body safety.
The child meaning is the recursive induction hypothesis; it is not asserted
by functionShape or silently assumed as a completed Checking theorem. -/
theorem observation_child_transport (inputs : Inputs s) (Z : Family s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (invocation : binder.kind = .invocation) (state : Decoded s View)
    (decoded : decode readout environment = some state) (observation : CheckGoal)
    (target : state.assignment.descriptor observation.upper = (state.callRow binder).descriptor)
    (child : ∀ candidate, Admitted inputs readout admissions environment binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs Z next observation)
    (challenge : Challenge (state.callRow binder)) (admitted : CheckedDomain inputs challenge)
    (view : View) (presented : state.viewMeaning view = challenge.carrierView)
    (readback : readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge view)) =
      (state.callRow binder).event)
    (occurrence : Nat) :
    ∀ raw, ObservationMem inputs Z
      (challenge.retarget (state.assignment.descriptor observation.lower)) raw →
        ObservationMem inputs Z challenge raw := by
  let candidate := scopeCandidate environment occurrence (.runtime (.invocation (encodeInvocation challenge view)))
  have accepted : Admitted inputs readout admissions environment binder candidate :=
    original_challenge_supplies_admission inputs readout admissions environment binder invocation
      state decoded challenge admitted view presented readback occurrence
  let next := (state.runtime readout binder (.invocation (encodeInvocation challenge view))).retain
    ⟨binder, candidate, environment.eventPath⟩
  have nextDecoded : decode readout (environment.extend binder candidate) = some next := by
    simpa only [candidate, scopeCandidate, decodeFrame, next] using
      decode_extend readout environment binder candidate state decoded
  have observed := child candidate accepted next nextDecoded
  change ObservationMeaning inputs Z
    (state.runtime readout binder (.invocation (encodeInvocation challenge view))) observation at observed
  simp only [ObservationMeaning, runtime_invocation_captures_input] at observed
  change ∀ raw, ObservationMem inputs Z
      (inputChallenge ((encodeInvocation challenge view).challenge
        (readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge view)))
        (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input
        (state.assignment.descriptor observation.lower)) raw →
      ObservationMem inputs Z
      (inputChallenge ((encodeInvocation challenge view).challenge
        (readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge view)))
        (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input
        (state.assignment.descriptor observation.upper)) raw at observed
  rw [readback] at observed
  have roundtrip := decode_encode_challenge challenge view state.viewMeaning presented
  change (encodeInvocation challenge view).challenge (state.callRow binder).event
    (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning = challenge at roundtrip
  rw [roundtrip] at observed
  change ∀ raw, ObservationMem inputs Z
      (challenge.retarget (state.assignment.descriptor observation.lower)) raw →
      ObservationMem inputs Z (challenge.retarget (state.assignment.descriptor observation.upper)) raw at observed
  rw [target] at observed
  exact observed

/-- The legacy source-admitted finite Function constructor and its same-provider semantic
step. Both recursive Checking children are retained in the resulting proof.
Their semantic induction hypotheses are explicit; this theorem does not
claim the primitive/structural cases of the full Checking induction. -/
theorem function_checking_constructor (inputs : Inputs s) (Z : Family s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (goal domain observation : CheckGoal) (binder : Binder)
    (shape : FunctionShape inputs readout environment goal domain binder observation)
    (domainChecked : Checking (functionKernel inputs readout admissions original) environment domain)
    (observationChecked : ∀ candidate,
      Admitted inputs readout admissions environment binder candidate →
        Checking (functionKernel inputs readout admissions original)
          (environment.extend binder candidate) observation)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (domainMeaning : DomainMeaning inputs state domain)
    (targetReadback : (state.callRow binder).descriptor = state.assignment.descriptor goal.upper)
    (observationMeaning : ∀ candidate, Admitted inputs readout admissions environment binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs Z next observation)
    (token : s.Receipt → View)
    (viewReadback : ∀ challenge : Challenge (state.callRow binder),
      inputs.checkedIncidences challenge → state.viewMeaning (token challenge.receipt) = challenge.carrierView)
    (eventReadback : ∀ challenge : Challenge (state.callRow binder), inputs.checkedIncidences challenge →
      readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge (token challenge.receipt))) =
        (state.callRow binder).event)
    (occurrence : Nat)
    (source : FunctionAt inputs Z ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower)))
    (guards : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      (inputs.functionGuards (state.goalRow binder goal) provider).Valid)
    (captures : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      (inputs.capturedFields (state.goalRow binder goal) provider).Holds Z) :
    Checking (functionKernel inputs readout admissions original) environment goal ∧
      FunctionAt inputs Z (state.goalRow binder goal) := by
  have rowSame : state.goalRow binder goal = state.callRow binder := by
    simp only [Decoded.goalRow, Decoded.callRow, ValueRow.withDescriptor] at targetReadback ⊢
    rw [targetReadback]
  rw [rowSame] at source guards captures ⊢
  refine ⟨Checking.function goal domain observation binder shape.domainMode shape.observationMode
    shape.invocationKind shape domainChecked observationChecked, ?_⟩
  obtain ⟨other, otherDecoded, _, _, _⟩ := shape.decoded
  have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
  subst other
  apply same_provider_function_check inputs Z (state.callRow binder)
    (state.assignment.descriptor goal.lower) source guards captures
  · intro challenge admitted
    have domainProof := domainMeaning
    unfold DomainMeaning at domainProof
    rw [shape.domainLower, shape.domainUpper, ← targetReadback] at domainProof
    exact domainProof _ _ challenge admitted
  · intro challenge admitted
    have incidence := admitted.2.2.2.2.1
    have transported := observation_child_transport inputs Z readout admissions environment binder
      shape.invocationKind state decoded observation
      (by simpa only [shape.observationUpper] using targetReadback.symm)
      observationMeaning challenge admitted (token challenge.receipt)
      (viewReadback challenge incidence) (eventReadback challenge incidence) occurrence
    rw [shape.observationLower] at transported
    exact transported

/-- The actual Received packet and original owned Receipt reconstruct the
same raw challenge encoding. No semantic view is substituted for its token. -/
theorem native_received_encoding {s : Sorts} {Key SiteData : Type}
    {row : ValueRow (nativeReceiptSorts s Key SiteData)} (challenge : Challenge row)
    (argument : SourceIdentityWorld.Received s.Carrier)
    (receipt : SourceIdentityWorld.Receipt Key SiteData)
    (carrier : challenge.carrier = argument.value) (owned : challenge.receipt = receipt) :
    nativeInvocation (encodeInvocation challenge argument.view) argument receipt =
      encodeInvocation challenge argument.view := by
  cases row
  cases challenge
  simp_all [nativeInvocation, encodeInvocation]

/-- A real native receipt insertion supplies the complete source candidate;
the remaining view/event equations are the original semantic field readback,
not merely equality of a Nat token or a promised source typing derivation. -/
theorem native_received_supplies_admission [DecidableEq Key]
    (inputs : Inputs (nativeReceiptSorts s Key SiteData))
    (readout : RuntimeReadout (nativeReceiptSorts s Key SiteData) Nat)
    (admissions : LocalAdmissions (nativeReceiptSorts s Key SiteData) Nat)
    (environment : Environment (Payload (nativeReceiptSorts s Key SiteData) Nat))
    (binder : Binder) (invocation : binder.kind = .invocation)
    (state : Decoded (nativeReceiptSorts s Key SiteData) Nat)
    (decoded : decode readout environment = some state)
    (challenge : Challenge (state.callRow binder)) (admitted : CheckedDomain inputs challenge)
    (receiving : SourceIdentityWorld.Receiving Key s.Carrier ViewData SiteData)
    (argument : SourceIdentityWorld.Received s.Carrier)
    (owner : SourceIdentityWorld.Owner) (site : SiteData) (formal : Option Key)
    (carrier : challenge.carrier = argument.value)
    (owned : challenge.receipt = {owner := owner, view := argument.view, site := site, formal := formal})
    (viewReadback : state.viewMeaning argument.view = challenge.carrierView)
    (eventReadback : readout.event state.fixedFrames state.assignment.event binder
      (.invocation (encodeInvocation challenge argument.view)) = (state.callRow binder).event)
    (occurrence : Nat) :
    Admitted inputs readout admissions environment binder
      (scopeCandidate environment occurrence (.runtime (.invocation
        (nativeInvocation (encodeInvocation challenge argument.view) argument
          {owner := owner, view := argument.view, site := site, formal := formal})))) ∧
    (receiving.record owner argument.view site formal).receipts.cell receiving.receipts.size =
      some {owner := owner, view := argument.view, site := site, formal := formal} := by
  rw [native_received_encoding challenge argument _ carrier owned]
  exact ⟨original_challenge_supplies_admission inputs readout admissions environment binder invocation
    state decoded challenge admitted argument.view viewReadback eventReadback occurrence,
    native_receipt_token_owned receiving owner argument.view site formal⟩

/-- A publication exposes both actual entry and completed retained state.
Its aliases share this complete object projection, not merely a name string. -/
structure Published (s : Sorts) (View : Type) where
  identity : PublicationId (Payload s View)
  entry : Actual s View
  completed : Actual s View
  captures : List (Name × PublicationId (Payload s View))

def publicationData (root : Root s View) (record : PublicationRecord (Payload s View)) :
    Published s View :=
  ⟨record.identity, record.entryFrames.foldl actualFrame root.decoded.actual,
    record.fixedFrames.foldl actualFrame root.decoded.actual, record.captures⟩

def published (environment : Environment (Payload s View)) (name : Name) :
    Option (Published s View) := do
  let root ← match environment.root with | .root data => some data | _ => none
  let identity ← environment.publicationName name
  let record ← environment.publications identity
  return publicationData root record

/-- Full published-entry/completed-state readback is computed from the
original stored prefixes, independent of arbitrary semantic readout maps. -/
theorem publication_data_matches_fold (readout : RuntimeReadout s View)
    (root : Root s View) (record : PublicationRecord (Payload s View)) :
    (publicationData root record).entry =
      (record.entryFrames.foldl (decodeFrame readout) root.decoded).actual ∧
    (publicationData root record).completed =
      (record.fixedFrames.foldl (decodeFrame readout) root.decoded).actual ∧
    (publicationData root record).captures = record.captures := by
  exact ⟨(actual_frames readout root.decoded record.entryFrames).symm,
    (actual_frames readout root.decoded record.fixedFrames).symm, rfl⟩

theorem alias_preserves_complete_publication
    (environment next : Environment (Payload s View)) (original aliasName : Name)
    (aliased : environment.aliasPublication original aliasName = some next) :
    published next aliasName = published environment original := by
  cases found : environment.publicationName original with
  | none => simp [Environment.aliasPublication, found] at aliased
  | some identity =>
      simp [Environment.aliasPublication, found] at aliased
      subst next
      simp only [published, found]
      simp [Environment.publicationName]

/-- Every observer of the installed object graph, completed captures or
creation state sees the same object through an alias. -/
theorem alias_preserves_publication_observers
    (environment next : Environment (Payload s View)) (original aliasName : Name)
    (aliased : environment.aliasPublication original aliasName = some next)
    (observe : Published s View → Result) :
    (published next aliasName).map observe = (published environment original).map observe := by
  rw [alias_preserves_complete_publication environment next original aliasName aliased]

theorem logical_preserves_fixed_prefix (state : Decoded s View) (data : Logical s View) :
    (state.logical data).fixedFrames = state.fixedFrames := rfl

theorem objects_preserve_fixed_prefix (state : Decoded s View) (entries : List (Endpoint × Object s)) :
    (entries.foldl Decoded.object state).fixedFrames = state.fixedFrames := by
  induction entries generalizing state with
  | nil => rfl
  | cons first rest ih =>
      rw [List.foldl_cons, ih]
      rcases first with ⟨endpoint, object⟩
      cases object <;> rfl

theorem runtime_preserves_prior_fixed_prefix (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    (state.runtime readout binder data).fixedFrames = state.fixedFrames :=
  objects_preserve_fixed_prefix state data.endpoints

/-- The entire original Shared field, including its witness and precise
binder/entry-path metadata, remains available to subsequent runtime readouts. -/
theorem shared_frame_retains_whole_witness (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Shared s)
    (event : ActualEvent (Payload s View)) (entryPath : List (EventStep (Payload s View))) :
    (decodeFrame readout state ⟨binder, ⟨.shared data, event⟩, entryPath⟩).fixedFrames =
      state.fixedFrames ++ [⟨binder, ⟨.shared data, event⟩, entryPath⟩] := rfl

def retainsFrame (frame : Frame (Payload s View)) : Bool :=
  match frame.value.data with
  | .shared _ | .runtime _ => true
  | _ => false

theorem decoded_frame_fixed_prefix (readout : RuntimeReadout s View)
    (state : Decoded s View) (frame : Frame (Payload s View)) :
    (decodeFrame readout state frame).fixedFrames =
      state.fixedFrames ++ (if retainsFrame frame then [frame] else []) := by
  cases payload : frame.value.data with
  | root data => simp only [decodeFrame, retainsFrame, payload, Bool.false_eq_true, ite_false, List.append_nil]
  | logical kind data =>
      simp only [decodeFrame, retainsFrame, payload, Bool.false_eq_true, ite_false,
        logical_preserves_fixed_prefix, List.append_nil]
  | shared data =>
      simp only [decodeFrame, retainsFrame, payload, ite_true, Decoded.retain, Decoded.shared]
  | runtime data =>
      simp only [decodeFrame, retainsFrame, payload, ite_true, Decoded.retain,
        runtime_preserves_prior_fixed_prefix]

theorem decoded_fixed_prefix (readout : RuntimeReadout s View)
    (state : Decoded s View) (frames : List (Frame (Payload s View))) :
    (frames.foldl (decodeFrame readout) state).fixedFrames =
      state.fixedFrames ++ frames.filter retainsFrame := by
  induction frames generalizing state with
  | nil => simp only [List.foldl_nil, List.filter_nil, List.append_nil]
  | cons first rest ih =>
      rw [List.foldl_cons, ih, decoded_frame_fixed_prefix]
      cases keep : retainsFrame first <;> simp [keep, List.append_assoc]

theorem retains_original_fixed_class (frame : Frame (Payload s View))
    (typed : frame.value.data.atKind frame.binder.kind) :
    retainsFrame frame = frame.binder.isFixed := by
  cases payload : frame.value.data with
  | root data => simp only [payload, Payload.atKind] at typed
  | logical kind data =>
      simp only [payload, Payload.atKind] at typed
      cases kind <;> simp [retainsFrame, payload, Binder.isFixed, Binder.isEvent,
        ← typed, LogicalKind.binderKind]
  | shared data =>
      simp only [payload, Payload.atKind] at typed
      simp [retainsFrame, payload, Binder.isFixed, Binder.isEvent, typed]
  | runtime data =>
      simp only [payload, Payload.atKind] at typed
      cases data <;> simp [retainsFrame, payload, Binder.isFixed, Binder.isEvent,
        ← typed, Runtime.kind]

theorem decoded_original_fixed_prefix (readout : RuntimeReadout s View)
    (state : Decoded s View) (frames : List (Frame (Payload s View)))
    (typed : ∀ frame ∈ frames, frame.value.data.atKind frame.binder.kind) :
    (frames.foldl (decodeFrame readout) state).fixedFrames =
      state.fixedFrames ++ frames.filter (fun frame => frame.binder.isFixed) := by
  rw [decoded_fixed_prefix]
  apply congrArg (fun rest => state.fixedFrames ++ rest)
  apply List.filter_congr
  intro frame member
  exact retains_original_fixed_class frame (typed frame member)

/-- Restore uses the original entry prefix for Shared readout; the completed
fixed history remains in the separate replay map and is not preinstalled. -/
theorem restore_retains_entry_witness_prefix (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (root : Root s View)
    (rootData : environment.root = .root root) (typed : TypedFrames environment)
    (record : PublicationRecord (Payload s View)) :
    (decode readout (environment.restore record)).map (fun state => state.fixedFrames) =
      some (record.entryFrames.filter retainsFrame) := by
  have actual := restore_decodes_actual_entry readout environment root rootData typed record
  have projected := congrArg (fun value => value.map (fun state => state.fixedFrames)) actual
  simpa only [Option.map_map, Function.comp_def, Decoded.actual, Option.map_some,
    decoded_fixed_prefix, Root.decoded, List.nil_append] using projected

end YulangClosure.OriginalSourceEnvironment
