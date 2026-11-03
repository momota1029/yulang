import YulangClosure.SourceGraphRegistrationR297
import YulangClosure.ComputedCallUnionClausesR308

/-!
Selected EI-Form / EI-Tail / EI-All syntax at actual R297 source occurrences.
Authority: computed-call-result-constructor (2026-10-24) §§2–4. GR1 supplies
its source/addressing specification, not a semantic operand or a source proof.

`prepare` is a source-owned, scoped FORMATION REQUEST: it records every missing
operand. `form` needs independent static formation evidence. Neither function
registers an element of opaque `s.Interface`, supplies EI-Intro, changes the
original synthesis endpoint, nor asserts that an arbitrary source is well typed.
The available original Positive receiver clauses are constructed separately;
the missing original phase/argument/IF interpreter is reported explicitly.
-/
namespace YulangClosure.ComputedCallTypedFormationR310

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open SourceGraphRegistrationR297

/-- An App row keeps the ORIGINAL scoped children and all local premises.
The row recognizer also checks the original sourceCallIncidence owner. -/
structure CallRecord where
  position : Position
  site : Site
  context : Context
  premises : List Premise
  callee : Program
  argument : Program
  calleeSite : Site
  argumentSite : Site

def callRecord (row : Row) : Option CallRecord :=
  match row.program with
  | .rule position .app site context premises (.cons callee (.cons argument .nil)) => do
      match row.callOwner with
      | some (.application _ _ calleeSite argumentSite) =>
          some ⟨position, site, context, premises, callee, argument, calleeSite, argumentSite⟩
      | _ => none
  | _ => none

def callTable (origin : Declaration) (context : Context) (raw : Source category) : List CallRecord :=
  (sourceInventory origin context raw).filterMap callRecord

/-- Syntactic local EI binders supplement the ORIGINAL Position telescope.
These are not invented runtime SourceEvents owner rows or event witnesses. -/
inductive LocalBinder where
  | calRet (call : Position)
  | carrier (call : Position)
  | challenge (call : Position)
  | receipt (call : Position)
  | response (call : Position)
  | future (call : Position)
  deriving DecidableEq, Repr

inductive OperandSort where
  | computation | function | challenge | inlet | argument | incidence
  deriving DecidableEq, Repr

/-- Sorts are disjoint even if an opaque original interpretation later maps
several references to the same semantic object. -/
inductive Slot : OperandSort → Type where
  | originalComputation (endpoint : Endpoint) : Slot .computation
  | completeResult : Slot .computation
  | arm (tag : Nat) (endpoint : Endpoint) : Slot .computation
  | checkedFunction (endpoint : Endpoint) : Slot .function
  | challenge : Slot .challenge
  | inlet : Slot .inlet
  | argument : Slot .argument
  | incidence : Slot .incidence
  deriving DecidableEq, Repr

structure Ref (scope : List LocalBinder) (sort : OperandSort) where
  position : Position
  slot : Slot sort
  deriving DecidableEq, Repr

/-- Existential packaging preserves the sort AND the entire local telescope. -/
structure Key where
  scope : List LocalBinder
  sort : OperandSort
  reference : Ref scope sort
  deriving DecidableEq, Repr

def Ref.key {scope : List LocalBinder} {sort : OperandSort} (reference : Ref scope sort) : Key :=
  ⟨scope, sort, reference⟩

theorem ref_key_injective {scope : List LocalBinder} {sort : OperandSort}
    (first second : Ref scope sort) (same : first.key = second.key) : first = second := by
  cases same
  rfl

/-- Position equality retains route, original telescope, and description frame.
Equal numeric source sites alone are never a key equality premise. -/
theorem key_position {scope : List LocalBinder} {sort : OperandSort}
    (first second : Ref scope sort) (same : first.key = second.key) :
    first.position = second.position := by
  exact congrArg Ref.position (ref_key_injective first second same)

/-- Only the actual Call's CalRet binder encloses this schema. The inert
argument is the ORIGINAL Program, including its captures, origin and premises;
no successful argument execution is substituted for it. -/
structure ArgumentSchema (scope : List LocalBinder) (call : Position) where
  original : Program
  reference : Ref (scope ++ [.calRet call]) .argument

structure Operands (scope : List LocalBinder) (call : Position) where
  callee : Ref scope .computation
  function : Ref scope .function
  challenge : Ref scope .challenge
  inlet : Ref scope .inlet
  argument : ArgumentSchema scope call
  incidence : Ref scope .incidence

/-- Original independent arm positions are retained, including duplicate
endpoint addresses and arm-specific lexical/event scopes. -/
structure Arm (scope : List LocalBinder) where
  tag : Nat
  originalScope : Position
  localBinders : List LocalBinder
  descriptor : Ref (scope ++ localBinders) .computation

inductive Computation : List LocalBinder → Type where
  | reference {scope} (reference : Ref scope .computation) : Computation scope
  | evalInvoke {scope} (call : Position) (operands : Operands scope call) : Computation scope
  | invokeTail {scope} (call : Position) (operands : Operands scope call) :
      Computation (scope ++ [.calRet call])
  | allArms {scope} (source : Computation scope) (arms : List (Arm scope)) : Computation scope

/-- The static premises of EI-Form remain separate from source membership,
carrier checking truth, provider acceptance, Q and logical admission. -/
structure StaticFormation (declared : Key → Prop) {scope : List LocalBinder}
    {call : Position} (operands : Operands scope call) : Prop where
  callee : declared operands.callee.key
  function : declared operands.function.key
  challenge : declared operands.challenge.key
  inlet : declared operands.inlet.key
  argument : declared operands.argument.reference.key
  incidence : declared operands.incidence.key

inductive Formed (declared : Key → Prop) : {scope : List LocalBinder} →
    Computation scope → Prop where
  | reference {scope} (reference : Ref scope .computation) (formed : declared reference.key) :
      Formed declared (.reference reference)
  | evalInvoke {scope call} (operands : Operands scope call)
      (formed : StaticFormation declared operands) : Formed declared (.evalInvoke call operands)
  | invokeTail {scope call} (operands : Operands scope call)
      (formed : StaticFormation declared operands) : Formed declared (.invokeTail call operands)
  | allArms {scope} (source : Computation scope) (arms : List (Arm scope))
      (sourceFormed : Formed declared source)
      (armFormed : ∀ arm ∈ arms, declared arm.descriptor.key) :
      Formed declared (.allArms source arms)

/-- A request retains the original result/check addresses; generatedResult is
an additional static constructor label, never a replacement synthesis value. -/
structure Request where
  original : CallRecord
  operands : Operands [] original.position
  originalResult : Endpoint
  originalCheck : Endpoint
  generatedResult : Ref [] .computation

/-- Addresses are allocated from the actual row position. Child computation
means the child's original synthesis interface, not its returned Value row. -/
def programPosition : Program → Position
  | .rule position .. | .initializerE position .. | .publishGroup position ..
  | .atPublication position .. | .aliasPublication position .. | .choice position .. => position
  | .existsE occurrence _ | .forallE occurrence _ | .executionE occurrence _
  | .sharedE occurrence _ => occurrence.position

def prepare (call : CallRecord) : Request where
  original := call
  operands := {
    callee := ⟨programPosition call.callee, .originalComputation ⟨call.calleeSite, .synthesis⟩⟩
    function := ⟨call.position, .checkedFunction ⟨call.site, .descriptor⟩⟩
    challenge := ⟨call.position, .challenge⟩
    inlet := ⟨call.position, .inlet⟩
    argument := ⟨call.argument, ⟨call.position, .argument⟩⟩
    incidence := ⟨call.position, .incidence⟩ }
  originalResult := ⟨call.site, .synthesis⟩
  originalCheck := ⟨call.site, .callableImage⟩
  generatedResult := ⟨call.position, .completeResult⟩

def requests (origin : Declaration) (context : Context) (raw : Source category) : List Request :=
  (callTable origin context raw).map prepare

/-- No default [] for arms: even the no-arm case needs its original owner's
complete arm-list formation. The supplied list is preserved verbatim. -/
def resultExpression (request : Request) (arms : List (Arm [])) : Computation [] :=
  .allArms (.evalInvoke request.original.position request.operands) arms

theorem form (declared : Key → Prop) (request : Request) (arms : List (Arm []))
    (operands : StaticFormation declared request.operands)
    (armFormation : ∀ arm ∈ arms, declared arm.descriptor.key) :
    Formed declared (resultExpression request arms) :=
  .allArms _ _ (.evalInvoke _ operands) armFormation

theorem form_tail (declared : Key → Prop) (request : Request)
    (operands : StaticFormation declared request.operands) :
    Formed declared (.invokeTail request.original.position request.operands) :=
  .invokeTail _ operands

theorem argument_scope (call : CallRecord) :
    (prepare call).operands.argument.reference.key.scope = [.calRet call.position] := rfl

theorem argument_original (call : CallRecord) :
    (prepare call).operands.argument.original = call.argument := rfl

theorem original_result_retained (call : CallRecord) :
    (prepare call).originalResult = ⟨call.site, .synthesis⟩ ∧
    (prepare call).originalCheck = ⟨call.site, .callableImage⟩ := ⟨rfl, rfl⟩

/-- Erasure removes only added constructor requests, returning the SAME source
program. It performs no endpoint updates or source-typing reconstruction. -/
structure PreparedSource where
  program : Program
  requests : List Request

def prepareSource (origin : Declaration) (context : Context) (raw : Source category) : PreparedSource :=
  ⟨source origin context raw, requests origin context raw⟩

theorem erase_prepared (origin : Declaration) (context : Context) (raw : Source category) :
    (prepareSource origin context raw).program.erase = sourceRules context raw :=
  erase_allocate _ _

/-- Exact original App equation, exposing its existing private annotation
wrapper without depending on that wrapper's private implementation name. -/
theorem source_app_equation (context : Context) (site : Site)
    (callee argument : Source .expression) :
    sourceRules context (.app ⟨site, none⟩ callee argument) =
      .existsE ⟨site, .viewLogic, 0⟩
        (LogicalOccurrencesR104.appRule context ⟨site, none⟩ callee argument) := by
  simp only [sourceRules]
  rfl

theorem source_name_equation (site : Site) (name : Name) :
    sourceRules [] (.name ⟨site, none⟩ name) =
      .rule .name site []
        [.atom {(atom .resolvedSameBinding site []) with names := [name]},
         .atom {(atom .computedFetchOnce site []) with names := [name]}] .nil := by
  simp only [sourceRules]
  rfl

/-- A concrete computed source is used only for this construction receipt;
the general source traversal and the parent judgment remain unrestricted. -/
def computedFixture : Source .expression :=
  ComputedCallSourceSupplierR294.computedSource 10 11 12

/-- Both actual Call addresses and their exact local CalRet scopes compute
from R297, with no supplied occurrence lookup or selected success assignment. -/
theorem computed_positions :
    (requests 7 [] computedFixture).map
      (fun request => (request.original.position, request.originalResult,
        request.operands.argument.reference.key.scope)) =
    [(⟨7, [0], [.existsE ⟨4, .viewLogic, 0⟩], []⟩, ⟨4, .synthesis⟩,
      [.calRet ⟨7, [0], [.existsE ⟨4, .viewLogic, 0⟩], []⟩]),
     (⟨7, [0, 0, 0], [.existsE ⟨4, .viewLogic, 0⟩, .existsE ⟨2, .viewLogic, 0⟩], []⟩,
       ⟨2, .synthesis⟩,
       [.calRet ⟨7, [0, 0, 0],
         [.existsE ⟨4, .viewLogic, 0⟩, .existsE ⟨2, .viewLogic, 0⟩], []⟩])] := by
  simp only [requests, callTable, sourceInventory, source, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, source_app_equation,
    LogicalOccurrencesR104.appRule, source_name_equation]
  rfl

def Request.sourceExpression (request : Request) : Computation [] :=
  .evalInvoke request.original.position request.operands

/-- The source expression is present even while its original all-arm family
is unresolved. `none` never means that there were zero original arms. -/
structure ResultRow where
  request : Request
  sourceExpression : Computation []
  completeExpression : Option (Computation [])

def resultTable (origin : Declaration) (context : Context) (raw : Source category)
    (originalArms : CallRecord → Option (List (Arm []))) : List ResultRow :=
  (requests origin context raw).map fun request =>
    ⟨request, request.sourceExpression,
      (originalArms request.original).map (resultExpression request)⟩

/-- Exact computation of a genuine outer computed-App source expression.
The witness is the actual first request, not an assumed desired lookup. -/
theorem computed_outer_expression :
    ∃ request, (requests 7 [] computedFixture)[0]? = some request ∧
      request.original.position = ⟨7, [0], [.existsE ⟨4, .viewLogic, 0⟩], []⟩ ∧
      request.operands.callee.position =
        ⟨7, [0, 0], [.existsE ⟨4, .viewLogic, 0⟩], []⟩ ∧
      request.sourceExpression = .evalInvoke request.original.position request.operands := by
  simp only [requests, callTable, sourceInventory, source, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, source_app_equation,
    LogicalOccurrencesR104.appRule, source_name_equation]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- No static full arm inventory is available in R297's source rows. Keeping
its lookup open does not infer a no-arm EI-All instance. -/
theorem unknown_arms_stay_unknown (origin : Declaration) (context : Context)
    (raw : Source category) :
    (resultTable origin context raw (fun _ => none)).map ResultRow.completeExpression =
      (requests origin context raw).map (fun _ => none) := by
  simp only [resultTable, List.map_map, Function.comp_def, Option.map_none]

/-- Erasure applies directly to the ORIGINAL R159 parent, preserving arbitrary
children, both annotation alternatives, and their ONE shared extension. -/
theorem erased_app_parent (kernel : Kernel Value) (environment : Environment Value)
    (origin : Declaration) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    Satisfies kernel environment (compile
      (prepareSource origin context (.app mark callee argument)).program.erase) ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel environment premise) ∧
      ∃ candidate, kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
        let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
        (∀ premise ∈ SourceAppAdmissionR159.appPremises context mark callee argument,
          Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧
        SourceJudgment kernel after context argument := by
  rw [erase_prepared]
  change Satisfies kernel environment (Build context (.app mark callee argument)) ↔ _
  rw [source_reconstruction, SourceAppAdmissionR159.app_source_iff]
  simp only [SourceAppAdmissionR159.app_continuation_iff]

/-- The original opaque semantic sorts are unchanged. CalRet data holds a
complete original returned row/provider and the actual callee observation;
this DATA does not assert that the callee really returned it. -/
structure CalRet (s : Sorts) where
  returned : ValueRow s
  provider : s.Provider
  callee : RawObservation s

/-- Available original post-CalRet receiver clause. Every original independent
challenge and every actual development survives; acceptance is a conclusion,
never an extra filter in the quantified challenge domain. Argument formation,
IF transport, prefix history and phase registration remain separate. -/
def receiverBody (inputs : Inputs s) (returned : ValueRow s) (provider : s.Provider) : Positive s :=
  .both (.guard (inputs.actual returned.value returned.root provider))
    (.both (functionClause inputs returned)
      (.all {challenge : Challenge returned // CheckedDomain inputs challenge} fun challenge =>
        .both (.guard (ActualAdm inputs provider challenge.val))
          (.all {raw : RawObservation s // inputs.execute provider challenge.val.input raw} fun raw =>
            inputs.checkedObservation challenge.val raw.val)))

theorem receiver_body_iff (inputs : Inputs s) (Z : Family s)
    (returned : ValueRow s) (provider : s.Provider) :
    (receiverBody inputs returned provider).Holds Z ↔
      inputs.actual returned.value returned.root provider ∧ FunctionAt inputs Z returned ∧
      ∀ challenge : Challenge returned, CheckedDomain inputs challenge →
        ActualAdm inputs provider challenge ∧
          ∀ raw, inputs.execute provider challenge.input raw →
            (inputs.checkedObservation challenge raw).Holds Z := by
  simp only [receiverBody, Positive.Holds, functionClause_iff, Subtype.forall]

/-- Actual F membership supplies this receiver component for the SAME actual
provider. This does not supply the earlier CalRet/Delay or source derivation. -/
theorem receiver_from_function (inputs : Inputs s) (returned : ValueRow s)
    (provider : s.Provider) (actual : inputs.actual returned.value returned.root provider)
    (form : inputs.valueForm returned.descriptor = .function)
    (member : Meaning inputs (.value returned)) :
    (receiverBody inputs returned provider).Holds (Meaning inputs) := by
  have body := (meaning_clause inputs (.value returned)).mp member
  have functionBody : FunctionAt inputs (Meaning inputs) returned := by
    simpa only [valueCore, form, functionClause_iff] using body.1
  exact (receiver_body_iff inputs _ returned provider).mpr
    ⟨actual, functionBody, fun d checked => (functionBody.2 provider actual).2.2 d checked⟩

/-- Cursor data is indexed by the original checked Function descriptor. These
are raw data carriers, not proofs of source phase registration. `receiver`
retains the original Challenge with ALL context/continuation/receipt fields;
its original checkedObservation includes all Value/Retained/Operation,
Request/resume, result and future alternatives without enumerating events. -/
inductive Cursor (s : Sorts) (function : s.Descriptor) where
  | callee (whole callee : RawObservation s)
  | calRet (whole : RawObservation s) (returned : CalRet s)
  | argument (whole : RawObservation s) (returned : CalRet s) (carrier : CarrierRow s)
  | receiver (whole : RawObservation s) (returned : CalRet s)
      (challenge : Challenge (returned.returned.withDescriptor function))
      (observation : RawObservation s)

/-- Exact unresolved OPERANDS, never a desired semantic equation. The first
missing schema has an original source owner and a fully scoped reference. -/
inductive Missing where
  | functionSort (reference : Key)
  | argumentSchema (reference : Key)
  | wholeInterface (reference : Key)
  | phaseRegistration (call : Position)
  | originalArms (call : Position)
  | resultRegistration (reference : Key)
  deriving DecidableEq, Repr

/-- Partial original Positive interpretation. A nonempty unresolved list is
part of every result: the available clauses are not mislabeled DescMem(EI).
There is no arbitrary supplied Positive, law oracle, or success default. -/
structure InterpretationAttempt (s : Sorts) where
  available : Positive s
  firstMissing : Missing
  furtherMissing : List Missing

def availableCalRet (inputs : Inputs s) (callee : s.Interface)
    (function : s.Descriptor) (returned : CalRet s) : Positive s :=
  .both (clause inputs (.trace (returned.callee.atInterface callee)))
    (.both (.guard (inputs.traceForm (returned.callee.atInterface callee) =
      .pureReturn returned.returned))
      (receiverBody inputs (returned.returned.withDescriptor function) returned.provider))

/-- This reads only the original callee synthesis/checked descriptor addresses
in the SAME Decoded environment. It does not reinterpret an endpoint as a
complete new constructor or add inhabitants to any original semantic sort. -/
def attemptInterpretation (inputs : Inputs s) (state : Decoded s View)
    (request : Request)
    (cursor : Cursor s (state.assignment.descriptor ⟨request.original.site, .descriptor⟩)) :
    InterpretationAttempt s :=
  let callee := state.interfaces ⟨request.original.calleeSite, .synthesis⟩
  let function := state.assignment.descriptor ⟨request.original.site, .descriptor⟩
  let available := match cursor with
    | .callee _ raw => clause inputs (.trace (raw.atInterface callee))
    | .calRet _ returned => availableCalRet inputs callee function returned
    | .argument _ returned carrier =>
        .both (availableCalRet inputs callee function returned)
          (clause inputs (.carrier carrier))
    | .receiver _ returned challenge observation =>
        .both (availableCalRet inputs callee function returned)
          (inputs.checkedObservation challenge observation)
  ⟨available,
    (if inputs.valueForm function = .function then
      .argumentSchema request.operands.argument.reference.key
    else .functionSort request.operands.function.key),
    [.wholeInterface request.operands.incidence.key,
     .phaseRegistration request.original.position,
     .originalArms request.original.position,
     .resultRegistration request.generatedResult.key]⟩

/-- After the original function-sort test succeeds, the first unimplemented
staged clause is the CalRet-local argument schema. Complete-computation sort
registration is an earlier STATIC premise of `form`, not established here. -/
theorem first_missing_argument (inputs : Inputs s) (state : Decoded s View)
    (request : Request)
    (functionSort : inputs.valueForm
      (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) = .function)
    (cursor : Cursor s (state.assignment.descriptor ⟨request.original.site, .descriptor⟩)) :
    (attemptInterpretation inputs state request cursor).firstMissing =
      .argumentSchema request.operands.argument.reference.key := by
  simp only [attemptInterpretation, functionSort, ↓reduceIte]

/-- A failed original function-sort readout remains a failure, even if a
caller supplies runtime cursor data. No nominal Ref tag overrides it. -/
theorem wrong_function_sort (inputs : Inputs s) (state : Decoded s View)
    (request : Request)
    (wrong : inputs.valueForm
      (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) ≠ .function)
    (cursor : Cursor s (state.assignment.descriptor ⟨request.original.site, .descriptor⟩)) :
    (attemptInterpretation inputs state request cursor).firstMissing =
      .functionSort request.operands.function.key := by
  simp only [attemptInterpretation, wrong, ↓reduceIte]

/-- Callee-stage interpretation uses exactly the original full trace clause;
this is an actual original fold/unfold, not EI registration. -/
theorem callee_readback (inputs : Inputs s) (state : Decoded s View)
    (request : Request) (whole raw : RawObservation s) :
    ((attemptInterpretation inputs state request (.callee whole raw)).available).Holds
        (Meaning inputs) ↔
      Meaning inputs (.trace (raw.atInterface
        (state.interfaces ⟨request.original.calleeSite, .synthesis⟩))) :=
by
  change (clause inputs (.trace (raw.atInterface
    (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)))).Holds (Meaning inputs) ↔ _
  exact (meaning_clause inputs _).symm

/-- Apply R293's ACTUAL original alternative introduction at the retained
original address. This theorem does not identify that address with EI. The
independent full arm endpoint list remains an explicit original-owner input. -/
theorem original_union_parent (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (state : Decoded s View)
    (request : Request) (arms : List Endpoint) (raw : RawObservation s) :
    Proof inputs registry leaves
      (.field (.trace (raw.atInterface (state.interfaces request.originalCheck))))
      (ComputedCallUnionRealizationR293.unionBody inputs state request.originalCheck arms raw) :=
  ComputedCallUnionRealizationR293.union_introduction inputs registry leaves state
    request.originalCheck arms raw

end YulangClosure.ComputedCallTypedFormationR310
