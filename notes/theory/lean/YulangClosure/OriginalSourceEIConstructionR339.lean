import YulangClosure.OriginalSourceEIInterpretationR331
import YulangClosure.OriginalSourceEvents

/-!
R339: parametric response/current-world construction at the original R311
callee-request consumer. EI §§3.1,3.4,5 and IF §§3.1–3.3,6 permit independent
original primitive typing and lawful actions as parameters. They do not permit
a completed EI clause, contribution, or target Checking as a parameter.

The response domain below precedes EI membership and provider acceptance. Every
original compatible current world, typed response, original admission, receipt,
and shared joint field is retained. This does not choose a concrete W/Z meaning.
The original schema must still be authenticated by its declaration owner.

LIMIT: this closes the typed universal callee-request construction edge of R311,
not the full Code→Generated interpreter. Receiver-result construction, semantic
scoped-reference resolution, primitive authentication and licensed source/arm
contributions remain separate; no R159 closure is asserted.
-/
namespace YulangClosure.OriginalSourceEIConstructionR339

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking ComputedCallTypedFormationR310
open OriginalComputedCallInterpretationR311 OriginalSourceEIInterpretationR331

variable {s : Sorts} {View : Type}

/-- Original request data before binding its response. The prior raw tuple,
actual handle, continuation and unexecuted suffix are distinct fields. -/
structure RequestHead (s : Sorts) (View : Type) where
  prior : RawObservation s
  original : Invocation s View
  otherEnvironment : s.Context
  operation : Declaration
  rawHandle : s.Continuation
  continuation : s.Continuation
  suffix : s.Context

/-- Independent original response signature, not an EI predicate. `Typed` and
`Admitted` are the original primitive's judgments at the LIVE current world.
`Response` can be infinite and dependent on the actual declaration. `observe`
is its original raw response projection; it asserts neither return nor safety. -/
structure ResponseSchema (s : Sorts) (View : Type) where
  Response : Declaration → Type
  Typed : (head : RequestHead s View) → Event s → Response head.operation → Prop
  Admitted : (head : RequestHead s View) → Event s → Response head.operation → Prop
  observe : (head : RequestHead s View) → Event s → Response head.operation → s.Observation
  /-- Original continuation relation: all zero/pending/finite developments,
  not a total function promising a Return. -/
  Develops : (head : RequestHead s View) → Event s → Response head.operation →
    RawObservation s → Prop

/-- Complete dependent response telescope. Receipt poststate is tied to the
same current event; the retained shared fields are not replaced by one local
frame or by a selected world. Typing/admission use no EI interpretation. -/
structure ResponseAt (inputs : Inputs s) (schema : ResponseSchema s View)
    (head : RequestHead s View) where
  current : Event s
  compatible : inputs.compatible head.prior.event current
  response : schema.Response head.operation
  typed : schema.Typed head current response
  admitted : schema.Admitted head current response
  receipt : ReceiptData s View
  currentHistory : receipt.after.history = current.history
  currentConfiguration : receipt.after.configuration = current.current
  retainedWitness : s.WitnessValue
  retainedNames : List (Name × Nat)
  retainedObjects : List (Nat × Installed s)
  resumed : RawObservation s
  development : schema.Develops head current response resumed

/-- The actual original record constructor, with the complete request data and
response/current tuple. In particular `current` does not become the prior event. -/
def ResponseAt.record {inputs : Inputs s} {schema : ResponseSchema s View}
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    OriginalSourceEvents.Response s View :=
  ⟨head.original, head.otherEnvironment, head.prior.observation, head.operation,
    head.rawHandle, head.continuation, head.suffix,
    ⟨schema.observe head answer.current answer.response, answer.receipt⟩,
    ⟨answer.current, answer.retainedWitness, answer.retainedNames, answer.retainedObjects⟩⟩

def ResponseAt.raw {inputs : Inputs s} {schema : ResponseSchema s View}
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) : RawObservation s :=
  answer.resumed

/-- All three current-state projections agree by construction; no equality
between pre-request and post-response configurations is imposed. -/
theorem response_current_exact {inputs : Inputs s} {schema : ResponseSchema s View}
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    answer.record.joint.event = answer.current ∧
    answer.record.response.receipt.after.history = answer.current.history ∧
    answer.record.response.receipt.after.configuration = answer.current.current :=
  ⟨rfl, answer.currentHistory, answer.currentConfiguration⟩

theorem request_fields_retained {inputs : Inputs s} {schema : ResponseSchema s View}
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    answer.record.request = head.prior.observation ∧
    answer.record.rawHandle = head.rawHandle ∧
    answer.record.continuation = head.continuation ∧
    answer.record.suffix = head.suffix ∧
    answer.record.otherEnvironment = head.otherEnvironment ∧
    answer.record.original = head.original := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every independently typed/admitted compatible response enters the domain,
without an EI, provider-acceptance, source-execution or returning-result test. -/
def responseAt (inputs : Inputs s) (schema : ResponseSchema s View)
    (head : RequestHead s View) (current : Event s)
    (compatible : inputs.compatible head.prior.event current)
    (response : schema.Response head.operation) (typed : schema.Typed head current response)
    (admitted : schema.Admitted head current response) (receipt : ReceiptData s View)
    (history : receipt.after.history = current.history)
    (configuration : receipt.after.configuration = current.current)
    (witness : s.WitnessValue) (names : List (Name × Nat))
    (objects : List (Nat × Installed s)) (resumed : RawObservation s)
    (development : schema.Develops head current response resumed) : ResponseAt inputs schema head :=
  ⟨current, compatible, response, typed, admitted, receipt, history, configuration,
    witness, names, objects, resumed, development⟩

/-- Exact expansion of the domain. In particular neither a chosen native
response nor successful callee termination replaces the independent quantifiers. -/
theorem all_original_responses_iff (inputs : Inputs s) (schema : ResponseSchema s View)
    (head : RequestHead s View) (P : RawObservation s → Prop) :
    (∀ answer : ResponseAt inputs schema head, P answer.raw) ↔
    (∀ current, inputs.compatible head.prior.event current →
      ∀ response, schema.Typed head current response → schema.Admitted head current response →
      ∀ (receipt : ReceiptData s View), receipt.after.history = current.history →
        receipt.after.configuration = current.current →
      ∀ (witness : s.WitnessValue) (names : List (Name × Nat))
        (objects : List (Nat × Installed s)) (raw : RawObservation s),
        schema.Develops head current response raw → P raw) := by
  constructor
  · intro all current compatible response typed admitted receipt history configuration witness names objects raw development
    exact all (responseAt inputs schema head current compatible response typed admitted
      receipt history configuration witness names objects raw development)
  · intro all answer
    exact all answer.current answer.compatible answer.response answer.typed answer.admitted
      answer.receipt answer.currentHistory answer.currentConfiguration answer.retainedWitness
      answer.retainedNames answer.retainedObjects answer.resumed answer.development

/-- Genuine callee component laws at one raw tuple. This is factored exactly
into original callee membership, original prefix primitive and the independently
typed same-return/provider/whole-argument inputs already exposed in R331. -/
structure CalleeInputs (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (raw : RawObservation s) where
  member : Meaning inputs (.trace (raw.atInterface
    (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)))
  prefixInput : PrimitiveInput inputs registry resolution
    (primitiveGoal request declarations .calleePrefix [.observation raw, .event raw.event])
  returns : ∀ returned : BoundReturn s request.original.position,
    registry.original (primitiveGoal request declarations .calleeResume
      ([.observation raw, .event raw.event] ++ returnedOperands returned)).signature →
    ReturnInputs inputs registry resolution leaves request declarations
      (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)
      (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) returned

/-- Each response is interpreted by its ORIGINAL callee contract. The full
EI body is constructed below, not supplied by `CalleeInputs`. -/
theorem callee_from_components (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (raw : RawObservation s)
    (original : CalleeInputs inputs registry resolution leaves state request declarations raw) :
    (calleePhaseBody inputs registry resolution state request declarations raw).Holds (Meaning inputs) :=
  callee_phase_from_original_operands inputs registry resolution leaves children state request
    declarations raw original.member original.prefixInput original.returns

/-- Universal response elimination into the EXISTING R311 calleeRequest case.
There is no picked response, completed phaseBody, EI membership or licensed child
input. Both old and resumed callee bodies are constructed from original operands.
The independent world/response/receipt/shared-field quantifiers remain inside
`ResponseAt` throughout; the resumed trace retains its own development event. -/
theorem every_typed_callee_response (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (schema : ResponseSchema s View) (head : RequestHead s View)
    (prior : CalleeInputs inputs registry resolution leaves state request declarations head.prior)
    (requested : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .calleeRequest
        [.observation head.prior, .event head.prior.event]))
    (resume : ∀ answer : ResponseAt inputs schema head,
      PrimitiveInput inputs registry resolution
        (primitiveGoal request declarations .calleeResume
          [.observation head.prior, .event head.prior.event,
           .observation answer.raw, .event answer.raw.event]))
    (callee : ∀ answer : ResponseAt inputs schema head,
      CalleeInputs inputs registry resolution leaves state request declarations answer.raw) :
    ∀ answer : ResponseAt inputs schema head,
      (phaseBody inputs registry resolution state request declarations
        (.calleeRequest head.prior answer.raw)).Holds (Meaning inputs) := by
  intro answer
  exact ⟨callee_from_components inputs registry resolution leaves children state request declarations
      head.prior prior,
    primitive_input_sound inputs registry resolution _ requested _,
    primitive_input_sound inputs registry resolution _ (resume answer) _,
    callee_from_components inputs registry resolution leaves children state request declarations
      answer.raw (callee answer)⟩

/-- Actual R330 source occurrence application. The full original arm inventory
is retained in the registered expression; none of its independent laws is
inferred from the callee branch. -/
theorem selected_registered_responses (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (origin : Declaration) (declared : Key → Prop)
    (definition : OriginalSourceViewRegistrationR330.Definition origin declared)
    (declarations : PrimitiveDeclarations) (schema : ResponseSchema s View) (head : RequestHead s View)
    (prior : CalleeInputs inputs registry resolution leaves state
      (OriginalSourceViewRegistrationR330.request origin) declarations head.prior)
    (requested : PrimitiveInput inputs registry resolution
      (primitiveGoal (OriginalSourceViewRegistrationR330.request origin) declarations .calleeRequest
        [.observation head.prior, .event head.prior.event]))
    (resume : ∀ answer : ResponseAt inputs schema head, PrimitiveInput inputs registry resolution
      (primitiveGoal (OriginalSourceViewRegistrationR330.request origin) declarations .calleeResume
        [.observation head.prior, .event head.prior.event,
         .observation answer.raw, .event answer.raw.event]))
    (callee : ∀ answer : ResponseAt inputs schema head,
      CalleeInputs inputs registry resolution leaves state
        (OriginalSourceViewRegistrationR330.request origin) declarations answer.raw) :
    (OriginalSourceViewRegistrationR330.register definition).read
      (OriginalSourceViewRegistrationR330.owner origin)
      (OriginalSourceViewRegistrationR330.request origin).generatedResult.key =
        some (OriginalInterfacePreservationR328.Selected.resultCode origin definition.arms) ∧
    ∀ answer : ResponseAt inputs schema head,
      (phaseBody inputs registry resolution state (OriginalSourceViewRegistrationR330.request origin)
        declarations (.calleeRequest head.prior answer.raw)).Holds (Meaning inputs) :=
  ⟨OriginalSourceViewRegistrationR330.registered_readback definition,
    every_typed_callee_response inputs registry resolution leaves children state _ declarations
      schema head prior requested resume callee⟩

/-- Field actions of an independently lawful original restriction. This record
contains NO action on a response telescope, phase clause or EI evidence. Those
composite actions are constructed below. Atomic invocation/receipt/installed
maps are the original component actions, not inferred from equal endpoints. -/
structure FieldMap (s : Sorts) (View : Type) where
  event : Event s → Event s
  observation : s.Observation → s.Observation
  invocation : Invocation s View → Invocation s View
  context : s.Context → s.Context
  declaration : Declaration → Declaration
  continuation : s.Continuation → s.Continuation
  receipt : ReceiptData s View → ReceiptData s View
  witness : s.WitnessValue → s.WitnessValue
  name : Name → Name
  address : Nat → Nat
  installed : Installed s → Installed s

def FieldMap.raw (f : FieldMap s View) (raw : RawObservation s) : RawObservation s :=
  ⟨f.observation raw.observation, f.event raw.event⟩

def FieldMap.head (f : FieldMap s View) (head : RequestHead s View) : RequestHead s View :=
  ⟨f.raw head.prior, f.invocation head.original, f.context head.otherEnvironment,
    f.declaration head.operation, f.continuation head.rawHandle,
    f.continuation head.continuation, f.context head.suffix⟩

def FieldMap.joint (f : FieldMap s View) (joint : OriginalSourceEvents.Joint s) :
    OriginalSourceEvents.Joint s :=
  ⟨f.event joint.event, f.witness joint.retainedWitness,
    joint.retainedNames.map (fun pair => (f.name pair.1, f.address pair.2)),
    joint.retainedObjects.map (fun pair => (f.address pair.1, f.installed pair.2))⟩

/-- Whole original record action is emitted by the original Response constructor.
All fields are mapped once; no coordinate can borrow another arm's provider or
another response's current world. -/
def FieldMap.record (f : FieldMap s View) (record : OriginalSourceEvents.Response s View) :
    OriginalSourceEvents.Response s View :=
  ⟨f.invocation record.original, f.context record.otherEnvironment,
    f.observation record.request, f.declaration record.operation,
    f.continuation record.rawHandle, f.continuation record.continuation,
    f.context record.suffix,
    ⟨f.observation record.response.observation, f.receipt record.response.receipt⟩,
    f.joint record.joint⟩

def FieldMap.identity : FieldMap s View :=
  ⟨id, id, id, id, id, id, id, id, id, id, id⟩

def FieldMap.then (first second : FieldMap s View) : FieldMap s View :=
  ⟨second.event ∘ first.event, second.observation ∘ first.observation,
    second.invocation ∘ first.invocation, second.context ∘ first.context,
    second.declaration ∘ first.declaration, second.continuation ∘ first.continuation,
    second.receipt ∘ first.receipt, second.witness ∘ first.witness,
    second.name ∘ first.name, second.address ∘ first.address,
    second.installed ∘ first.installed⟩

theorem head_identity (head : RequestHead s View) : FieldMap.identity.head head = head := by
  cases head
  rfl

theorem head_composition (first second : FieldMap s View) (head : RequestHead s View) :
    (first.then second).head head = second.head (first.head head) := rfl

theorem record_identity (record : OriginalSourceEvents.Response s View) :
    FieldMap.identity.record record = record := by
  cases record with
  | mk original other request operation handle continuation suffix response joint =>
    cases response
    cases joint
    simp [FieldMap.record, FieldMap.joint, FieldMap.identity]

theorem record_composition (first second : FieldMap s View)
    (record : OriginalSourceEvents.Response s View) :
    (first.then second).record record = second.record (first.record record) := by
  simp only [FieldMap.record, FieldMap.joint, FieldMap.then, Function.comp_apply, List.map_map]
  rfl

/-- Genuine component naturality, at the independently specified primitive
signature. Typing, admission and raw response projection are separate laws.
No law mentions phaseBody, a generated field, source child or contribution. -/
structure LawfulResponseMap (inputs : Inputs s) (schema : ResponseSchema s View)
    (fields : FieldMap s View) where
  response : (declaration : Declaration) → schema.Response declaration →
    schema.Response (fields.declaration declaration)
  compatible : ∀ before after, inputs.compatible before after →
    inputs.compatible (fields.event before) (fields.event after)
  typed : ∀ head current value, schema.Typed head current value →
    schema.Typed (fields.head head) (fields.event current) (response head.operation value)
  admitted : ∀ head current value, schema.Admitted head current value →
    schema.Admitted (fields.head head) (fields.event current) (response head.operation value)
  observation : ∀ head current value,
    schema.observe (fields.head head) (fields.event current) (response head.operation value) =
      fields.observation (schema.observe head current value)
  development : ∀ head current value raw, schema.Develops head current value raw →
    schema.Develops (fields.head head) (fields.event current)
      (response head.operation value) (fields.raw raw)
  receiptCurrent : ∀ (receipt : ReceiptData s View) (current : Event s),
    receipt.after.history = current.history → receipt.after.configuration = current.current →
    (fields.receipt receipt).after.history = (fields.event current).history ∧
    (fields.receipt receipt).after.configuration = (fields.event current).current

/-- The typed whole action is constructed from component laws. It uses one
shared middle event/response/receipt in every dependent field. -/
def restrictResponse {inputs : Inputs s} {schema : ResponseSchema s View}
    (fields : FieldMap s View) (lawful : LawfulResponseMap inputs schema fields)
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    ResponseAt inputs schema (fields.head head) where
  current := fields.event answer.current
  compatible := lawful.compatible _ _ answer.compatible
  response := lawful.response head.operation answer.response
  typed := lawful.typed _ _ _ answer.typed
  admitted := lawful.admitted _ _ _ answer.admitted
  receipt := fields.receipt answer.receipt
  currentHistory := (lawful.receiptCurrent _ _ answer.currentHistory answer.currentConfiguration).1
  currentConfiguration := (lawful.receiptCurrent _ _ answer.currentHistory answer.currentConfiguration).2
  retainedWitness := fields.witness answer.retainedWitness
  retainedNames := answer.retainedNames.map (fun pair => (fields.name pair.1, fields.address pair.2))
  retainedObjects := answer.retainedObjects.map (fun pair => (fields.address pair.1, fields.installed pair.2))
  resumed := fields.raw answer.resumed
  development := lawful.development _ _ _ _ answer.development

/-- Whole-map naturality is a THEOREM of the constructor, not an extra global
map hypothesis. Only the primitive raw-response naturality law is used. -/
theorem response_restriction_natural {inputs : Inputs s} {schema : ResponseSchema s View}
    (fields : FieldMap s View) (lawful : LawfulResponseMap inputs schema fields)
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    (restrictResponse fields lawful answer).record = fields.record answer.record := by
  simp only [restrictResponse, ResponseAt.record, FieldMap.record, FieldMap.head,
    FieldMap.raw, FieldMap.joint]
  exact congrArg (fun observed =>
    OriginalSourceEvents.Response.mk (fields.invocation head.original)
      (fields.context head.otherEnvironment) (fields.observation head.prior.observation)
      (fields.declaration head.operation) (fields.continuation head.rawHandle)
      (fields.continuation head.continuation) (fields.context head.suffix)
      ⟨observed, fields.receipt answer.receipt⟩
      ⟨fields.event answer.current, fields.witness answer.retainedWitness,
        answer.retainedNames.map (fun pair => (fields.name pair.1, fields.address pair.2)),
        answer.retainedObjects.map (fun pair => (fields.address pair.1, fields.installed pair.2))⟩)
    (lawful.observation head answer.current answer.response)

theorem response_restriction_raw {inputs : Inputs s} {schema : ResponseSchema s View}
    (fields : FieldMap s View) (lawful : LawfulResponseMap inputs schema fields)
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    (restrictResponse fields lawful answer).raw = fields.raw answer.raw := by
  rfl

/-- Identity component maps are lawful without an EI assumption. -/
def identityLaw (inputs : Inputs s) (schema : ResponseSchema s View) :
    LawfulResponseMap inputs schema FieldMap.identity where
  response := fun _ value => value
  compatible := fun _ _ compatible => compatible
  typed := fun _ _ _ typed => typed
  admitted := fun _ _ _ admitted => admitted
  observation := by intro head current value; rfl
  development := fun _ _ _ _ development => development
  receiptCurrent := fun _ _ history configuration => ⟨history, configuration⟩

/-- Finite composition of lawful primitive restrictions supplies the whole
original response action; no restriction is converted into a returning run. -/
def composeLaw {inputs : Inputs s} {schema : ResponseSchema s View}
    (first second : FieldMap s View)
    (firstLaw : LawfulResponseMap inputs schema first)
    (secondLaw : LawfulResponseMap inputs schema second) :
    LawfulResponseMap inputs schema (first.then second) where
  response := fun declaration value => secondLaw.response _ (firstLaw.response declaration value)
  compatible := fun _ _ compatible => secondLaw.compatible _ _ (firstLaw.compatible _ _ compatible)
  typed := fun _ _ _ typed => secondLaw.typed _ _ _ (firstLaw.typed _ _ _ typed)
  admitted := fun _ _ _ admitted => secondLaw.admitted _ _ _ (firstLaw.admitted _ _ _ admitted)
  observation := by
    intro head current value
    change schema.observe (second.head (first.head head)) (second.event (first.event current))
      (secondLaw.response _ (firstLaw.response _ value)) = _
    exact (secondLaw.observation (first.head head) (first.event current)
      (firstLaw.response head.operation value)).trans
        (congrArg second.observation (firstLaw.observation head current value))
  development := fun _ _ _ _ development =>
    secondLaw.development _ _ _ _ (firstLaw.development _ _ _ _ development)
  receiptCurrent := by
    intro receipt current history configuration
    have firstCurrent := firstLaw.receiptCurrent _ _ history configuration
    exact secondLaw.receiptCurrent _ _ firstCurrent.1 firstCurrent.2

/-- Both the original complete record and its subsequent continuation
observation commute with composed restrictions. This is whole-data equality,
including the shared witness and all installed objects, not only effect rows. -/
theorem response_restriction_composition {inputs : Inputs s} {schema : ResponseSchema s View}
    (first second : FieldMap s View)
    (firstLaw : LawfulResponseMap inputs schema first)
    (secondLaw : LawfulResponseMap inputs schema second)
    {head : RequestHead s View} (answer : ResponseAt inputs schema head) :
    (restrictResponse second secondLaw (restrictResponse first firstLaw answer)).record =
      (restrictResponse (first.then second) (composeLaw first second firstLaw secondLaw) answer).record ∧
    (restrictResponse second secondLaw (restrictResponse first firstLaw answer)).raw =
      (restrictResponse (first.then second) (composeLaw first second firstLaw secondLaw) answer).raw := by
  constructor
  · rw [response_restriction_natural, response_restriction_natural,
      response_restriction_natural, record_composition]
  · rfl

/-- Applied to the actual R311 consumer AFTER a lawful whole restriction.
The component callee laws quantify at the changed original request/current
world. The old request world is not silently reused to prove them. -/
theorem restricted_callee_response (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (schema : ResponseSchema s View) (head : RequestHead s View)
    (fields : FieldMap s View) (lawful : LawfulResponseMap inputs schema fields)
    (prior : CalleeInputs inputs registry resolution leaves state request declarations (fields.raw head.prior))
    (requested : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .calleeRequest
        [.observation (fields.raw head.prior), .event (fields.event head.prior.event)]))
    (resume : ∀ answer : ResponseAt inputs schema (fields.head head),
      PrimitiveInput inputs registry resolution (primitiveGoal request declarations .calleeResume
        [.observation (fields.raw head.prior), .event (fields.event head.prior.event),
         .observation answer.raw, .event answer.raw.event]))
    (callee : ∀ answer : ResponseAt inputs schema (fields.head head),
      CalleeInputs inputs registry resolution leaves state request declarations answer.raw)
    (answer : ResponseAt inputs schema head) :
    (phaseBody inputs registry resolution state request declarations
      (.calleeRequest (fields.raw head.prior) (fields.raw answer.raw))).Holds (Meaning inputs) := by
  have result := every_typed_callee_response inputs registry resolution leaves children state request
    declarations schema (fields.head head) prior requested resume callee
    (restrictResponse fields lawful answer)
  rw [response_restriction_raw] at result
  exact result

end YulangClosure.OriginalSourceEIConstructionR339
