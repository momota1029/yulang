import YulangClosure.OriginalParameterWorld
import YulangClosure.OriginalParameterSemantics

/-!
Actual original Lambda Shared continuation, with a local native consumer.
The source shell is calculated from the raw Parameter. No caller supplies a
rule package, body derivation, post-bind registry equation or second witness.
-/
namespace YulangClosure.OriginalFormalShared

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalWorldReadout OriginalParameterWorld

variable {s : Sorts} {View : Type}

/-- Source-local body context, including the original formal role and pattern. -/
def formalContext (parameter : Parameter) : Context :=
  {name := parameter.formal.name, owner := parameter.formal.site, kind := .formal,
    annotation := parameter.formal.annotation, entry := some parameter.formal.entry,
    singleUse := parameter.body.nameCount parameter.formal.name == 1} :: parameter.context

def bodyContext (parameter : Parameter) : Context :=
  parameter.pattern.bindingRecords.filter (fun binding =>
    !((formalContext parameter).any (fun prior => prior.name == binding.name))) ++
    formalContext parameter

def checkedBody (parameter : Parameter) : RuleTree :=
  .rule .sequence parameter.formal.site (formalContext parameter) []
    (.two (sourceRules (formalContext parameter) parameter.pattern)
      (.existsE ⟨parameter.body.site, .eventProof, 0⟩
        (.rule .sequence parameter.body.site (bodyContext parameter)
          (([AtomKind.completeBodyConsumer, .actualReturnOrPendingSuffix].map
            (fun kind => .atom (atom kind parameter.body.site (bodyContext parameter)
              [parameter.lambdaSite, parameter.formal.site]))) ++
            [.checking ⟨.computation, parameter.body.site, bodyContext parameter,
              ⟨parameter.body.site, .finalRoot⟩, ⟨parameter.lambdaSite, .bodyConsumer⟩⟩])
          (.one (sourceRules (bodyContext parameter) parameter.body)))))

def sharedBinder (parameter : Parameter) : Binder := ⟨parameter.formal.site, .shared, 0⟩
def returnBinder (parameter : Parameter) : Binder := ⟨parameter.formal.site, .returnRebind, 0⟩
def invocationBinder (parameter : Parameter) : Binder := ⟨parameter.lambdaSite, .invocation, 0⟩
def receiptBinder (parameter : Parameter) : Binder := ⟨parameter.formal.site, .receipt, 0⟩
def descriptionBinder (parameter : Parameter) : Binder := ⟨parameter.formal.site, .description, 0⟩
def viewBinder (parameter : Parameter) : Binder := ⟨parameter.lambdaSite, .viewLogic, 0⟩

def retainedBody (parameter : Parameter) : RuleTree :=
  .sharedE (sharedBinder parameter) (checkedBody parameter)

def enteredBody (parameter : Parameter) : RuleTree :=
  match parameter.formal.entry with
  | .value => .executionE (returnBinder parameter) (retainedBody parameter)
  | .computation => retainedBody parameter

def entryPremises (parameter : Parameter) : List Premise :=
  [.atom {(atom .sourceFormalRole parameter.formal.site (formalContext parameter)) with
    annotation := parameter.formal.annotation, entry := some parameter.formal.entry}] ++
  ((match parameter.formal.entry with
    | .value => [AtomKind.receiptFormation, .entryForceReturnRebind]
    | .computation => [.receiptFormation, .retainedEntry]).map
      (fun kind => .atom (atom kind parameter.formal.site (formalContext parameter)
        [parameter.lambdaSite, parameter.pattern.site, parameter.body.site])))

def lambdaTree (parameter : Parameter) : RuleTree :=
  .existsE (descriptionBinder parameter)
    (.existsE (viewBinder parameter)
      (.rule .lambda parameter.lambdaSite parameter.context
        ([AtomKind.captureWholeEnvironment, .closureFormation].map
          (fun kind => .atom (atom kind parameter.lambdaSite parameter.context
            [parameter.formal.site, parameter.pattern.site, parameter.body.site])))
        (.one (.forallE (invocationBinder parameter)
          (.existsE (receiptBinder parameter)
            (.rule .parameterEntry parameter.formal.site (formalContext parameter)
              (entryPremises parameter) (.one (enteredBody parameter))))))))

theorem actual_lambda_tree (parameter : Parameter) :
    sourceRules parameter.context parameter.source = lambdaTree parameter := by
  simp only [Parameter.source, sourceRules]
  rfl

/-- A source annotation contributes its original boundary premises; peeling
that wrapper does not discard or change the formal's own annotation. -/
theorem annotation_child (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (annotation : Option Declaration)
    (proof : SourceJudgment kernel environment parameter.context
      (.lambda ⟨parameter.lambdaSite, annotation⟩ parameter.formal parameter.pattern parameter.body)) :
    Judgment kernel environment (lambdaTree parameter) := by
  cases annotation with
  | none =>
      change Judgment kernel environment (sourceRules parameter.context parameter.source) at proof
      rw [actual_lambda_tree] at proof
      exact proof
  | some target =>
      simp only [SourceJudgment, sourceRules] at proof
      cases proof with
      | rule _ children =>
          cases children with
          | cons first _ =>
              exact first

/-- The actual original Build supplies both pre-invocation existential
frames, then every original admitted invocation, then its receipt and entry.
No replacement source tree or source-success premise is introduced. -/
theorem build_entry (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (annotation : Option Declaration)
    (solves : Satisfies kernel environment (Build parameter.context
      (.lambda ⟨parameter.lambdaSite, annotation⟩ parameter.formal parameter.pattern parameter.body))) :
    ∃ description, kernel.admitted environment (descriptionBinder parameter) description ∧
    ∃ view, kernel.admitted (environment.extend (descriptionBinder parameter) description)
      (viewBinder parameter) view ∧
    ∀ invocation, kernel.admitted
      ((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view)
      (invocationBinder parameter) invocation →
    ∃ receipt, kernel.admitted
      (((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend (invocationBinder parameter) invocation) (receiptBinder parameter) receipt ∧
      Judgment kernel
        ((((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend (invocationBinder parameter) invocation).extend (receiptBinder parameter) receipt)
        (enteredBody parameter) := by
  have source := (source_reconstruction kernel environment parameter.context _).mp solves
  have proof := annotation_child kernel environment parameter annotation source
  cases proof with
  | existsE description descriptionAdmitted rest =>
      cases rest with
      | existsE view viewAdmitted closure =>
          refine ⟨description, descriptionAdmitted, view, viewAdmitted, ?_⟩
          cases closure with
          | rule _ children =>
              cases children with
              | cons invocationProof _ =>
                  cases invocationProof with
                  | forallE every =>
                      intro invocation invocationAdmitted
                      cases every invocation invocationAdmitted with
                      | existsE receipt receiptAdmitted entryProof =>
                          refine ⟨receipt, receiptAdmitted, ?_⟩
                          cases entryProof with
                          | rule _ children =>
                              cases children with
                              | cons body _ => exact body

/-- Opening an actual invocation clears initializer replay. Its receipt
preserves that fact, so a Value formal uses the original open Return domain. -/
theorem invocation_receipt_open (environment : Environment Value) (parameter : Parameter)
    (invocation receipt : ScopedValue Value) :
    ((environment.extend (invocationBinder parameter) invocation).extend (receiptBinder parameter) receipt).replay = none := rfl

/-- At the designated Return continuation, the witness is the SAME anchor
already selected by the actual generated Shared rule. -/
theorem value_entry_shared (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (mode : parameter.formal.entry = .value)
    (openHistory : environment.replay = none)
    (entry : Judgment kernel environment (enteredBody parameter))
    (returned : ScopedValue Value)
    (admitted : kernel.admitted environment (returnBinder parameter) returned) :
    let after := environment.extend (returnBinder parameter) returned
    kernel.admitted after (sharedBinder parameter) (after.anchorValue (sharedBinder parameter)) ∧
    Judgment kernel (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter)))
      (checkedBody parameter) := by
  simp only [enteredBody, mode] at entry
  cases entry with
  | executionOpen _ every =>
      cases every returned admitted with
      | sharedE valid body => exact ⟨valid, body⟩
  | executionFixed history fixed _ _ _ _ =>
      rw [openHistory] at fixed
      cases fixed

/-- Computational entry retains the carrier at its receipt; it does not
invent a Force, a returned Value, or a value-cell allocation. -/
theorem computation_entry_shared (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (mode : parameter.formal.entry = .computation)
    (entry : Judgment kernel environment (enteredBody parameter)) :
    kernel.admitted environment (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter)) ∧
    Judgment kernel (environment.extend (sharedBinder parameter)
      (environment.anchorValue (sharedBinder parameter))) (checkedBody parameter) := by
  simp only [enteredBody, mode] at entry
  cases entry with
  | sharedE valid body => exact ⟨valid, body⟩

theorem physical_shared_binder (parameter : Parameter) :
    parameter.registration.physicalRetainedOwner.binder = sharedBinder parameter ∧
    parameter.registration.retainedOwner.binder = sharedBinder parameter := ⟨rfl, rfl⟩

/-- A locally admitted Shared anchor supplies its actual typed payload,
anchored parent path and decoder state. This uses no rich-key inverse. -/
theorem admitted_shared_payload (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (parameter : Parameter)
    (admitted : Admitted inputs readout admissions environment (sharedBinder parameter)
      (environment.anchorValue (sharedBinder parameter))) :
    ∃ state data,
      decode readout environment = some state ∧
      (environment.anchorValue (sharedBinder parameter)).data = .shared data ∧
      (environment.anchorValue (sharedBinder parameter)).event.parents = environment.eventPath ∧
      admissions.shared state (sharedBinder parameter) data := by
  obtain ⟨parents, state, decoded, valid⟩ := admitted
  cases payload : (environment.anchorValue (sharedBinder parameter)).data with
  | shared data =>
      rw [payload] at valid
      exact ⟨state, data, decoded, rfl, parents, valid.2⟩
  | root data => rw [payload] at valid; exact False.elim valid
  | logical kind data =>
      rw [payload] at valid
      cases kind <;> cases valid.1
  | runtime data =>
      rw [payload] at valid
      cases data <;> cases valid.1

/-- Actual anchor metadata determines the exact frame used by the decoder. -/
theorem anchor_as_scoped (environment : Environment (Payload s View)) (binder : Binder)
    (data : Payload s View) (payload : (environment.anchorValue binder).data = data)
    (parents : (environment.anchorValue binder).event.parents = environment.eventPath) :
    environment.anchorValue binder = scopeCandidate environment
      (environment.anchorValue binder).event.occurrence data := by
  cases h : environment.anchorValue binder with
  | mk actual event =>
      cases event with
      | mk prior occurrence =>
          simp only [h] at payload parents ⊢
          cases payload
          cases parents
          rfl


open NativeClosureEnvironment SourceIdentityWorld

/-- Raw selected-pair call operands, computed from the same source member.
The carrier graph and Force-start relation are independent operational inputs;
neither contains a logical observation membership or eventual Return test. -/
structure PairExecution (D ViewData Rest : Type) where
  pair : OriginalRecursivePair.SourcePair
  side : OriginalRecursivePair.Side
  carrier : OriginalRecursivePair.Carrier Nat D Nat ViewData Nat Rest
  start : World Nat D Nat ViewData Nat Rest → carrier.State → Prop
  initial : World Nat D Nat ViewData Nat Rest
  capturedEnvironment : Nat
  call : Nat
  argument : Received Nat

def PairExecution.parameter (execution : PairExecution D ViewData Rest)
    (declaration : Declaration) (ambient : List ScopeEntry) (outside : Context) : Parameter :=
  ⟨declaration, ambient, execution.pair.groupContext outside,
    execution.pair.lambda execution.side, execution.pair.formal execution.side,
    .varPattern (execution.pair.formalSite execution.side) (execution.pair.formalName execution.side),
    execution.pair.body execution.side⟩

def PairExecution.entry (execution : PairExecution D ViewData Rest) :
    OriginalRecursivePair.EntryData Nat Nat Nat :=
  ⟨execution.call, execution.pair.lambda execution.side,
    execution.pair.formalSite execution.side, execution.pair.formalName execution.side,
    execution.argument⟩

def PairExecution.plan (execution : PairExecution D ViewData Rest) :
    OriginalRecursivePair.BodyPlan Nat Nat :=
  execution.pair.plan execution.capturedEnvironment execution.side

theorem pair_parameter_source (execution : PairExecution D ViewData Rest)
    (declaration : Declaration) (ambient : List ScopeEntry) (outside : Context) :
    (execution.parameter declaration ambient outside).source =
      execution.pair.member execution.side := rfl

theorem pair_parameter_entry (execution : PairExecution D ViewData Rest)
    (declaration : Declaration) (ambient : List ScopeEntry) (outside : Context) :
    (execution.parameter declaration ambient outside).formal.entry = .value ∧
    execution.entry.formal = (execution.parameter declaration ambient outside).formal.name ∧
    execution.entry.slot = (execution.parameter declaration ambient outside).formal.site ∧
    execution.entry.provider = (execution.parameter declaration ambient outside).lambdaSite :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An actual completed Return at THIS original source continuation.
The history includes receipt and all arbitrary raw administrative/response
steps. Current delimiter identity is checked in the returned world; it is
not guessed to be the original delimiter after an intervening resumption. -/
def PairExecution.Returns (execution : PairExecution D ViewData Rest)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) : Prop :=
  ∃ count before,
    Prefix (OriginalRecursivePair.InvocationMove execution.carrier execution.entry
      execution.plan execution.start) count (.before execution.initial) (.running (.forcing before)) ∧
    execution.carrier.returned before packet ∧
    packet.world.control.current = .invocation packet.owner ∧
    ∃ delimiter, packet.world.control.invocations.cell packet.owner = some delimiter ∧
      delimiter.active = true ∧ delimiter.call = execution.entry.call ∧
      delimiter.provider = execution.entry.provider

/-- Construction from the primitive raw transition, not from a Returned
record's shape. No body check or Shared anchor occurs in the premises. -/
theorem operational_return_incidence (execution : PairExecution D ViewData Rest)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (count : Nat) (before : execution.carrier.State)
    (history : Prefix (OriginalRecursivePair.InvocationMove execution.carrier execution.entry
      execution.plan execution.start) count (.before execution.initial) (.running (.forcing before)))
    (returned : execution.carrier.returned before packet)
    (current : packet.world.control.current = .invocation packet.owner)
    (delimiter : SourceIdentityWorld.Invocation Nat)
    (registered : packet.world.control.invocations.cell packet.owner = some delimiter)
    (live : delimiter.active = true) (call : delimiter.call = execution.entry.call)
    (provider : delimiter.provider = execution.entry.provider) : execution.Returns packet :=
  ⟨count, before, history, returned, current, delimiter, registered, live, call, provider⟩

/-- The admitted Return has the authentic source-generated suffix. The
original current delimiter and raw returned value are retained unchanged. -/
theorem return_enters_original_suffix (execution : PairExecution D ViewData Rest)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (actual : execution.Returns packet) :
    ∃ count, Prefix (OriginalRecursivePair.InvocationMove execution.carrier execution.entry
      execution.plan execution.start) count (.before execution.initial)
        (.running (.suffix (packet.suffix execution.plan) (.entry packet.world packet.value))) := by
  obtain ⟨count, before, history, returned, _⟩ := actual
  exact ⟨count + 1, .snoc history (.running (.returned returned))⟩

/-- Every independently supplied raw history still has its original phase,
including pending/administrative/resumed prefixes that have no Return. -/
theorem all_prefixes_retained (execution : PairExecution D ViewData Rest)
    (count : Nat) (last : OriginalRecursivePair.InvocationState execution.carrier)
    (history : Prefix (OriginalRecursivePair.InvocationMove execution.carrier execution.entry
      execution.plan execution.start) count (.before execution.initial) last) :
    OriginalRecursivePair.InvocationWitness execution.carrier execution.entry execution.plan
      execution.start execution.initial last := OriginalRecursivePair.invocation_every_prefix history

/-- Data interpretation of this independently owned raw execution. These
fields do not assert world validity, admission, or any recursive membership.
A concrete all-source/native interpretation is not inferred from this record. -/
structure ReturnReadout (s : Sorts) (D ViewData Rest : Type) where
  assignment : ViewAssignment s Nat
  observation : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest → s.Observation
  after : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest → Current s
  endpoints : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest → List (Endpoint × Object s)
  bindings : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest → List (Name × Nat)

def ReturnReadout.outcome (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) : Outcome s :=
  (nativeReturned presentation.assignment packet.value (presentation.observation packet)
    (presentation.after packet) (presentation.endpoints packet)
    (presentation.bindings packet ++ [(parameter.formal.name, packet.world.cells.size)])).outcome

/-- The original returned packet computes the retained tuple. Its only
witness input is the witness already present in the actual Shared anchor. -/
def ReturnReadout.evidence (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (witness : s.WitnessValue) : Retained s parameter.registration :=
  nativeEvidence parameter selection mode presentation.assignment packet.world packet.value
    (presentation.observation packet) (presentation.after packet) (presentation.endpoints packet)
    (presentation.bindings packet ++ [(parameter.formal.name, packet.world.cells.size)]) witness

/-- Every operationally matching packet is represented, not just Some-result
records or a selected successful execution. The original incoming invocation
is matched independently of any description or Shared anchor. -/
def ReturnAdmission (execution : PairExecution D ViewData Rest)
    (presentation : ReturnReadout s D ViewData Rest) (parameter : Parameter)
    (invocation : OriginalSourceEnvironment.Invocation s View)
    (state : Decoded s View) (binder : Binder) (outcome : Outcome s) : Prop :=
  binder = returnBinder parameter ∧ state.activeRaw = some invocation ∧
    ∃ packet, execution.Returns packet ∧ outcome = presentation.outcome parameter packet

/-- Compute the exact Value tuple from the current Return's owned operands.
The address is the latest binding of this formal, and the contract was
selected before invocation. No raw-packet inverse or semantic success occurs. -/
def retainedValue (parameter : Parameter) (descriptor : s.Descriptor)
    (outcome : Outcome s) (witness : s.WitnessValue) : Option (Shared s) := do
  let object ← outcome.result
  match object with
  | .carrier _ _ => none
  | .value value root =>
      let binding ← outcome.bindings.reverse.find? (fun binding => binding.1 == parameter.formal.name)
      return ⟨[(parameter.formal.name, binding.2)],
        [(binding.2, .value descriptor value root)], witness⟩

/-- Constructor calculation on the SAME actual packet. This theorem does
not attempt to recover the raw Received value from its semantic projection. -/
theorem retained_native_outcome (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) (witness : s.WitnessValue) :
    retainedValue parameter (selection.valueDescriptor mode) (presentation.outcome parameter packet) witness =
      some ((presentation.evidence parameter selection mode packet witness).shared parameter.registration) := by
  simp only [retainedValue, ReturnReadout.outcome, nativeReturned, OriginalSourceEvents.Returned.outcome,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.find?_cons, beq_self_eq_true]
  change some (⟨[(parameter.formal.name, packet.world.cells.size)],
    [(packet.world.cells.size, .value (selection.valueDescriptor mode)
      (presentation.assignment.value packet.value.value) (presentation.assignment.root packet.value.value))], witness⟩ : Shared s) = _
  congr 1
  change _ = (⟨[(parameter.formal.name, (presentation.evidence parameter selection mode packet witness).address)],
    [((presentation.evidence parameter selection mode packet witness).address,
      (presentation.evidence parameter selection mode packet witness).data.installed)], witness⟩ : Shared s)
  rw [ReturnReadout.evidence, native_evidence_address, native_evidence_object]

/-- The exact immediately preceding Return payload computes retained Shared.
The operation's authenticity is established by ReturnAdmission; this local
field construction neither chooses another packet nor uses its safety. -/
def SharedAdmission (_execution : PairExecution D ViewData Rest)
    (_presentation : ReturnReadout s D ViewData Rest) (parameter : Parameter)
    (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View)
    (state : Decoded s View) (binder : Binder) (data : Shared s) : Prop :=
  binder = sharedBinder parameter ∧ state.activeRaw = some invocation ∧
    ∃ frame outcome, state.fixedFrames.getLast? = some frame ∧
      frame.binder = returnBinder parameter ∧
      frame.value.data = .runtime (.returnRebind outcome) ∧
      retainedValue parameter (selection.valueDescriptor mode) outcome data.witness = some data

/-- Local selected-owner admission. Other original predicates are retained.
This is only a local owner application: global rich-route discrimination in
legacy AnchorKey/Decoded is a separate, unproved representation obligation. -/
noncomputable def ownerAdmissions (base : LocalAdmissions s View)
    (execution : PairExecution D ViewData Rest) (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View) : LocalAdmissions s View := by
  classical
  exact {base with
    returnRebind := fun state binder outcome =>
      if binder = returnBinder parameter ∧ state.activeRaw = some invocation
      then ReturnAdmission execution presentation parameter invocation state binder outcome
      else base.returnRebind state binder outcome
    shared := fun state binder data =>
      if binder = sharedBinder parameter ∧ state.activeRaw = some invocation
      then SharedAdmission execution presentation parameter selection mode invocation state binder data
      else base.shared state binder data}

theorem actual_return_admitted (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (execution : PairExecution D ViewData Rest)
    (presentation : ReturnReadout s D ViewData Rest) (parameter : Parameter)
    (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View) (state : Decoded s View)
    (active : state.activeRaw = some invocation)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (actual : execution.Returns packet) :
    DataAdmitted inputs readout (ownerAdmissions base execution presentation parameter selection mode invocation)
      state (returnBinder parameter) (.runtime (.returnRebind (presentation.outcome parameter packet))) := by
  refine ⟨rfl, ?_⟩
  simp only [ownerAdmissions, active, and_self, ↓reduceIte]
  exact ⟨rfl, active, packet, actual, rfl⟩

/-- Pending outcomes remain in the raw carrier and general Outcome type, but
are not Returns at this designated operational continuation. -/
theorem pending_not_this_return (execution : PairExecution D ViewData Rest)
    (presentation : ReturnReadout s D ViewData Rest) (parameter : Parameter)
    (invocation : OriginalSourceEnvironment.Invocation s View) (state : Decoded s View)
    (binder : Binder) (outcome : Outcome s) (pending : outcome.result = none) :
    ¬ ReturnAdmission execution presentation parameter invocation state binder outcome := by
  rintro ⟨_, _, packet, _, equal⟩
  subst outcome
  cases pending

/-- Decoding the original Return extension retains the exact final frame.
All earlier fixed metadata survives; no equality of total witness functions. -/
def returnState (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (parameter : Parameter)
    (outcome : Outcome s) (occurrence : Nat) : Decoded s View :=
  decodeFrame readout state ⟨returnBinder parameter,
    scopeCandidate environment occurrence (.runtime (.returnRebind outcome)), environment.eventPath⟩

theorem return_state_frame (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (parameter : Parameter)
    (outcome : Outcome s) (occurrence : Nat) :
    (returnState readout state environment parameter outcome occurrence).fixedFrames =
      state.fixedFrames ++ [⟨returnBinder parameter,
        scopeCandidate environment occurrence (.runtime (.returnRebind outcome)), environment.eventPath⟩] := by
  exact congrArg (fun frames => frames ++ [_])
    (runtime_preserves_prior_fixed_prefix readout state (returnBinder parameter) (.returnRebind outcome))

theorem return_state_active (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (parameter : Parameter)
    (outcome : Outcome s) (occurrence : Nat) :
    (returnState readout state environment parameter outcome occurrence).activeRaw = state.activeRaw := rfl

/-- The actual generated anchor is decoded at the exit path of the exact
Return candidate. The proof compares constructors, not packet inverses. -/
theorem source_anchor_delivers (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (execution : PairExecution D ViewData Rest)
    (presentation : ReturnReadout s D ViewData Rest) (parameter : Parameter)
    (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (active : state.activeRaw = some invocation)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) (occurrence : Nat)
    (admitted : Admitted inputs readout
      (ownerAdmissions base execution presentation parameter selection mode invocation)
      (environment.extend (returnBinder parameter)
        (scopeCandidate environment occurrence (.runtime (.returnRebind (presentation.outcome parameter packet)))))
      (sharedBinder parameter)
      ((environment.extend (returnBinder parameter)
        (scopeCandidate environment occurrence (.runtime (.returnRebind (presentation.outcome parameter packet))))).anchorValue (sharedBinder parameter))) :
    let outcome := presentation.outcome parameter packet
    let after := environment.extend (returnBinder parameter)
      (scopeCandidate environment occurrence (.runtime (.returnRebind outcome)))
    let post := returnState readout state environment parameter outcome occurrence
    ∃ witness sharedOccurrence,
      decode readout (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) =
      some (deliverFrame readout post parameter
        (presentation.evidence parameter selection mode packet witness) after.eventPath sharedOccurrence) := by
  dsimp only at admitted ⊢
  let outcome := presentation.outcome parameter packet
  let after := environment.extend (returnBinder parameter)
    (scopeCandidate environment occurrence (.runtime (.returnRebind outcome)))
  let post := returnState readout state environment parameter outcome occurrence
  have afterDecoded : decode readout after = some post :=
    decode_extend readout environment (returnBinder parameter) _ state decoded
  obtain ⟨other, data, found, payload, parents, valid⟩ :=
    admitted_shared_payload inputs readout _ after parameter admitted
  have same := Option.some.inj (afterDecoded.symm.trans found)
  subst other
  have postActive : post.activeRaw = some invocation := active
  simp only [ownerAdmissions, postActive, and_self, ↓reduceIte] at valid
  obtain ⟨_, _, frame, actualOutcome, lastFrame, _, actualData, computed⟩ := valid
  have frames := return_state_frame readout state environment parameter outcome occurrence
  have lastActual : post.fixedFrames.getLast? = some ⟨returnBinder parameter,
      scopeCandidate environment occurrence (.runtime (.returnRebind outcome)), environment.eventPath⟩ := by
    rw [frames]
    simp
  have frameEq := Option.some.inj (lastFrame.symm.trans lastActual)
  subst frame
  have outcomeEq : outcome = actualOutcome := by cases actualData; rfl
  subst actualOutcome
  rw [retained_native_outcome] at computed
  have sameData := Option.some.inj computed
  refine ⟨data.witness, (after.anchorValue (sharedBinder parameter)).event.occurrence, ?_⟩
  change decode readout (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) = _
  have anchored := anchor_as_scoped after (sharedBinder parameter) (.shared data) payload parents
  rw [anchored]
  have useData := congrArg (fun shared => scopeCandidate after
    (after.anchorValue (sharedBinder parameter)).event.occurrence (Payload.shared shared)) sameData
  rw [← useData]
  exact deliver_existing_environment readout after post afterDecoded parameter
    (presentation.evidence parameter selection mode packet data.witness) _

/-- The exact source-provided decoder cell map agrees with actual native
allocation, provided the previous cell map represented the same pre-bind
world. The post-bind equation is derived, not an input. -/
theorem delivered_return_native (readout : RuntimeReadout s View) (state : Decoded s View)
    (presentation : ReturnReadout s D ViewData Rest) (parameter : Parameter)
    (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (cells : List (Option (Received Nat))) (actualCells : packet.world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout presentation.assignment packet.world.cells)
    (parent : Nat) (node : Node Nat D) (found : nodeAt packet.world.environments parent = some node)
    (witness : s.WitnessValue) (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    (deliverFrame readout state parameter (presentation.evidence parameter selection mode packet witness)
      parents occurrence).installed =
    bindingReadout (installValueContract presentation.assignment packet.world.cells.size
      (selection.valueDescriptor mode))
      (bindValue packet.world parent parameter.formal.name packet.value node found).cells :=
  delivered_native_bind_readout readout state parameter selection mode presentation.assignment packet.world
    cells actualCells represented parent parameter.formal.name packet.value node found
    (presentation.observation packet) (presentation.after packet) (presentation.endpoints packet)
    (presentation.bindings packet ++ [(parameter.formal.name, packet.world.cells.size)]) witness parents occurrence


/-- Runtime Return cannot choose another pre-invocation formal descriptor.
This is a data-preservation theorem, not a conversion or membership rule. -/
theorem return_keeps_selected_descriptor (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (parameter : Parameter)
    (outcome : Outcome s) (occurrence : Nat) :
    (returnState readout state environment parameter outcome occurrence).assignment.descriptor =
      state.assignment.descriptor :=
  runtime_preserves_descriptors readout state (returnBinder parameter) (.returnRebind outcome)

noncomputable def localKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (execution : PairExecution D ViewData Rest) (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View) : Kernel (Payload s View) :=
  OriginalCheckingAdmission.goalAdmissionKernel inputs readout
    (ownerAdmissions base execution presentation parameter selection mode invocation)
    (admissionKernel inputs readout
      (ownerAdmissions base execution presentation parameter selection mode invocation) original)

/-- Output property of the ACTUAL source entry. Inputs are a decoded incoming
state, a genuine operational Return, and the previous native cell invariant.
The native post-bind equation and checked source continuation are outputs. -/
def ReturnConsumer (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (execution : PairExecution D ViewData Rest) (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View)
    (environment : Environment (Payload s View)) : Prop :=
  ∀ (state : Decoded s View), decode readout environment = some state → state.activeRaw = some invocation →
  ∀ (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest), execution.Returns packet →
  ∀ occurrence,
    let outcome := presentation.outcome parameter packet
    let after := environment.extend (returnBinder parameter)
      (scopeCandidate environment occurrence (.runtime (.returnRebind outcome)))
    let post := returnState readout state environment parameter outcome occurrence
    ∃ witness sharedOccurrence,
      let delivered := deliverFrame readout post parameter
        (presentation.evidence parameter selection mode packet witness) after.eventPath sharedOccurrence
      decode readout (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) =
        some delivered ∧
      Judgment (localKernel inputs readout base original execution presentation parameter selection mode invocation)
        (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) (checkedBody parameter) ∧
      ∀ (cells : List (Option (Received Nat))), packet.world.cells = vectorStore cells →
        post.installed = bindingReadout presentation.assignment packet.world.cells →
        ∀ (node : Node Nat D) (found : nodeAt packet.world.environments execution.capturedEnvironment = some node),
          delivered.installed = bindingReadout
            (installValueContract presentation.assignment packet.world.cells.size (selection.valueDescriptor mode))
            (bindValue packet.world execution.capturedEnvironment parameter.formal.name packet.value node found).cells

theorem entry_actual_return_consumer (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (execution : PairExecution D ViewData Rest) (presentation : ReturnReadout s D ViewData Rest)
    (parameter : Parameter) (selection : Selected s View parameter) (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation s View)
    (environment : Environment (Payload s View)) (openHistory : environment.replay = none)
    (entry : Judgment (localKernel inputs readout base original execution presentation parameter selection mode invocation)
      environment (enteredBody parameter)) :
    ReturnConsumer inputs readout base original execution presentation parameter selection mode invocation environment := by
  intro state decoded active packet actual occurrence
  dsimp only
  have admitted : Admitted inputs readout
      (ownerAdmissions base execution presentation parameter selection mode invocation)
      environment (returnBinder parameter) (scopeCandidate environment occurrence
        (.runtime (.returnRebind (presentation.outcome parameter packet)))) :=
    (admitted_scoped_iff inputs readout _ environment _ state decoded occurrence _).mpr
      (actual_return_admitted inputs readout base execution presentation parameter selection mode invocation
        state active packet actual)
  have shared := value_entry_shared
    (localKernel inputs readout base original execution presentation parameter selection mode invocation)
    environment parameter mode openHistory entry _ admitted
  obtain ⟨witness, sharedOccurrence, delivered⟩ :=
    source_anchor_delivers inputs readout base execution presentation parameter selection mode invocation
      environment state decoded active packet occurrence shared.1
  refine ⟨witness, sharedOccurrence, delivered, shared.2, ?_⟩
  intro cells actualCells represented node found
  exact delivered_return_native readout _ presentation parameter selection mode packet cells actualCells represented
    execution.capturedEnvironment node found witness _ sharedOccurrence

/-- Original Build application for the selected pair's actual raw source.
The two description frames, complete invocation domain and receipt scope are
those of sourceRules. A ReturnConsumer is CONCLUDED for every entered source
scope; it is never supplied as an atom or premise of reconstruction. -/
theorem actual_build_pair_consumer (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (execution : PairExecution D ViewData Rest) (presentation : ReturnReadout s D ViewData Rest)
    (declaration : Declaration) (ambient : List ScopeEntry) (outside : Context)
    (selection : Selected s View (execution.parameter declaration ambient outside))
    (invocation : OriginalSourceEnvironment.Invocation s View)
    (environment : Environment (Payload s View)) (annotation : Option Declaration)
    (solves : Satisfies
      (localKernel inputs readout base original execution presentation
        (execution.parameter declaration ambient outside) selection rfl invocation)
      environment (Build (execution.pair.groupContext outside)
        (.lambda ⟨execution.pair.lambda execution.side, annotation⟩ (execution.pair.formal execution.side)
          (.varPattern (execution.pair.formalSite execution.side) (execution.pair.formalName execution.side))
          (execution.pair.body execution.side)))) :
    let parameter := execution.parameter declaration ambient outside
    let kernel := localKernel inputs readout base original execution presentation parameter selection rfl invocation
    ∃ description, kernel.admitted environment (descriptionBinder parameter) description ∧
    ∃ view, kernel.admitted (environment.extend (descriptionBinder parameter) description) (viewBinder parameter) view ∧
    ∀ incoming, kernel.admitted
      ((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view)
      (invocationBinder parameter) incoming →
    ∃ receipt, kernel.admitted
      (((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend
        (invocationBinder parameter) incoming) (receiptBinder parameter) receipt ∧
      ReturnConsumer inputs readout base original execution presentation parameter selection rfl invocation
        ((((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend
          (invocationBinder parameter) incoming).extend (receiptBinder parameter) receipt) := by
  dsimp only
  obtain ⟨description, descriptionAdmitted, view, viewAdmitted, every⟩ :=
    build_entry (localKernel inputs readout base original execution presentation
      (execution.parameter declaration ambient outside) selection rfl invocation)
      environment (execution.parameter declaration ambient outside) annotation solves
  refine ⟨description, descriptionAdmitted, view, viewAdmitted, ?_⟩
  intro incoming incomingAdmitted
  obtain ⟨receipt, receiptAdmitted, entry⟩ := every incoming incomingAdmitted
  refine ⟨receipt, receiptAdmitted, ?_⟩
  exact entry_actual_return_consumer inputs readout base original execution presentation
    (execution.parameter declaration ambient outside) selection rfl invocation _ rfl entry

/-- The physical generated Shared and virtual retained metadata agree on
binder and the actual Return exit key; their constructor routes stay distinct. -/
theorem actual_return_anchor (environment : Environment (Payload s View)) (parameter : Parameter)
    (candidate : ScopedValue (Payload s View)) :
    (environment.extend (returnBinder parameter) candidate).anchorKey
      parameter.registration.physicalRetainedOwner.binder =
      ⟨environment.origin, (⟨returnBinder parameter, candidate, environment.eventPath⟩ : Frame (Payload s View)).exitPath,
        parameter.registration.retainedOwner.binder⟩ := rfl


/-- The three source-owned phases before arbitrary Force are constructed,
not required as an unexplained execution-prefix premise. -/
theorem original_force_entry (execution : PairExecution D ViewData Rest)
    (first : execution.carrier.State)
    (started : execution.start
      (OriginalRecursivePair.receiveWorld
        (OriginalRecursivePair.enterWorld execution.initial execution.entry.call execution.entry.provider)
        execution.entry) first) :
    Prefix (OriginalRecursivePair.InvocationMove execution.carrier execution.entry execution.plan execution.start)
      3 (.before execution.initial) (.running (.forcing first)) :=
  .snoc (.snoc (.snoc (.refl _) (.begin _)) (.receipt _)) (.force started)

def PairExecution.receipt (execution : PairExecution D ViewData Rest) : Receipt Nat Nat :=
  ⟨.invocation execution.initial.control.invocations.size, execution.argument.view,
    execution.entry.slot, some execution.entry.formal⟩

/-- Canonical source receipt allocation agrees with the record used to
present the incoming invocation; the old world and all other receipts stay. -/
theorem constructed_original_receipt (execution : PairExecution D ViewData Rest) :
    (OriginalRecursivePair.receiveWorld
      (OriginalRecursivePair.enterWorld execution.initial execution.entry.call execution.entry.provider)
      execution.entry).receiving.receipts.cell execution.initial.receiving.receipts.size =
      some execution.receipt :=
  (OriginalRecursivePair.source_receipt_fields _ execution.entry).1

/-- A native-token incoming constructor under the existing concrete Receipt
sort. Context, continuation and typed path/incidence remain independent input
fields. This is data ownership, not proof of complete Call/domain admission. -/
def PairExecution.presentInvocation (execution : PairExecution D ViewData Rest)
    (assignment : ViewAssignment (nativeReceiptSorts s Nat Nat) Nat)
    (template : OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat) :
    OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat :=
  {nativeInvocation template
      ⟨assignment.carrier execution.argument.value, execution.argument.interface,
        execution.argument.view, execution.argument.dispatch⟩ execution.receipt with
    carrierRoot := assignment.root execution.argument.value}

theorem constructed_invocation_operands (execution : PairExecution D ViewData Rest)
    (assignment : ViewAssignment (nativeReceiptSorts s Nat Nat) Nat)
    (template : OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat) :
    (execution.presentInvocation assignment template).carrier = assignment.carrier execution.argument.value ∧
    (execution.presentInvocation assignment template).carrierRoot = assignment.root execution.argument.value ∧
    (execution.presentInvocation assignment template).view = execution.argument.view ∧
    (execution.presentInvocation assignment template).receipt = execution.receipt := ⟨rfl, rfl, rfl, rfl⟩

theorem constructed_invocation_independent_fields (execution : PairExecution D ViewData Rest)
    (assignment : ViewAssignment (nativeReceiptSorts s Nat Nat) Nat)
    (template : OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat) :
    (execution.presentInvocation assignment template).current = template.current ∧
    (execution.presentInvocation assignment template).value = template.value ∧
    (execution.presentInvocation assignment template).valueRoot = template.valueRoot ∧
    (execution.presentInvocation assignment template).context = template.context ∧
    (execution.presentInvocation assignment template).continuation = template.continuation ∧
    (execution.presentInvocation assignment template).path = template.path ∧
    (execution.presentInvocation assignment template).consumer = template.consumer ∧
    (execution.presentInvocation assignment template).incidence = template.incidence :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Instantiation at the same constructed carrier/view/receipt. Neither the
raw packet nor any independent template field is reconstructed by inversion. -/
theorem native_entry_return_admitted
    (inputs : Inputs (nativeReceiptSorts s Nat Nat))
    (readout : RuntimeReadout (nativeReceiptSorts s Nat Nat) Nat)
    (base : LocalAdmissions (nativeReceiptSorts s Nat Nat) Nat)
    (execution : PairExecution D ViewData Rest)
    (presentation : ReturnReadout (nativeReceiptSorts s Nat Nat) D ViewData Rest)
    (declaration : Declaration) (ambient : List ScopeEntry) (outside : Context)
    (selection : Selected (nativeReceiptSorts s Nat Nat) Nat (execution.parameter declaration ambient outside))
    (template : OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat)
    (state : Decoded (nativeReceiptSorts s Nat Nat) Nat)
    (active : state.activeRaw = some (execution.presentInvocation presentation.assignment template))
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (actual : execution.Returns packet) :
    DataAdmitted inputs readout
      (ownerAdmissions base execution presentation (execution.parameter declaration ambient outside) selection rfl
        (execution.presentInvocation presentation.assignment template))
      state (returnBinder (execution.parameter declaration ambient outside))
      (.runtime (.returnRebind (presentation.outcome (execution.parameter declaration ambient outside) packet))) :=
  actual_return_admitted inputs readout base execution presentation (execution.parameter declaration ambient outside)
    selection rfl (execution.presentInvocation presentation.assignment template) state active packet actual


/-! ## Same-packet application to the accepted concrete native world

Only the newly defined native presentation is used. No isomorphism with an
arbitrary old Configuration is asserted, and the computed event is not
silently identified with every decoded event. -/

open OriginalParameterSemantics

/-- Convert the same independent raw/logical value readouts between the
native presentation and its base sorts. All five fields are retained. -/
def baseViews (assignment : ViewAssignment (NS b D Nat ViewData Nat Rest Body View) Nat) :
    ViewAssignment b Nat :=
  ⟨assignment.descriptor, assignment.interface, assignment.value, assignment.carrier, assignment.root⟩

/-- A concrete current native presentation for the SAME actual raw packet.
The template supplies the complete current residual/provider/alias and typed
fields; the actual raw world and fixed cell readout are computed inputs. -/
def packetEvent (template : Event (NS b D Nat ViewData Nat Rest Body View))
    (presentation : ReturnReadout (NS b D Nat ViewData Nat Rest Body View) D ViewData Rest)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) :
    Event (NS b D Nat ViewData Nat Rest Body View) :=
  {template with
    current := {template.current with world := packet.world}
    eta := {template.eta with views := baseViews presentation.assignment}}

theorem packet_event_readout (template : Event (NS b D Nat ViewData Nat Rest Body View))
    (presentation : ReturnReadout (NS b D Nat ViewData Nat Rest Body View) D ViewData Rest)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) :
    (packetEvent template presentation packet).current.world = packet.world ∧
    viewAssignment (packetEvent template presentation packet).eta = presentation.assignment ∧
    installed (packetEvent template presentation packet) =
      bindingReadout presentation.assignment packet.world.cells := ⟨rfl, rfl, rfl⟩

/-- Registry agreement for the event constructed from that actual packet.
It is derived from both native bind constructors, never supplied as an
actualRegistry or desired post-world equality. -/
theorem delivered_packet_registry
    (readout : RuntimeReadout (NS b D Nat ViewData Nat Rest Body View) View)
    (state : Decoded (NS b D Nat ViewData Nat Rest Body View) View)
    (template : Event (NS b D Nat ViewData Nat Rest Body View))
    (presentation : ReturnReadout (NS b D Nat ViewData Nat Rest Body View) D ViewData Rest)
    (parameter : Parameter) (selection : Selected (NS b D Nat ViewData Nat Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest)
    (cells : List (Option (Received Nat))) (vector : packet.world.cells = vectorStore cells)
    (represented : state.installed = installed (packetEvent template presentation packet))
    (parent : Nat) (node : Node Name D) (found : nodeAt packet.world.environments parent = some node)
    (fields : EventFields b) (witness : b.WitnessValue)
    (parents : List (EventStep (Payload (NS b D Nat ViewData Nat Rest Body View) View))) (occurrence : Nat) :
    (deliverFrame readout state parameter (presentation.evidence parameter selection mode packet witness)
      parents occurrence).installed =
    installed (bindEvent (packetEvent template presentation packet) parent parameter.formal.name packet.value node found
      (selection.valueDescriptor mode) fields) :=
  delivered_return_native readout state presentation parameter selection mode packet cells vector represented
    parent node found witness parents occurrence

/-- The actual generated source consumer and the concrete complete PhiW
constructor meet at the same computed packet, address, A and retained value.
Recursive old-world/returned-field premises and original post-event guards
remain explicit; no completed Checking theorem is lifted to a hole family. -/
theorem actual_entry_packet_phiW
    (baseInputs : Inputs (NS b D Nat ViewData Nat Rest Body View))
    (references : Body → Nat → Option Name)
    (candidate : Family (NS b D Nat ViewData Nat Rest Body View))
    (readout : RuntimeReadout (NS b D Nat ViewData Nat Rest Body View) View)
    (baseAdmissions : LocalAdmissions (NS b D Nat ViewData Nat Rest Body View) View)
    (original : Kernel (Payload (NS b D Nat ViewData Nat Rest Body View) View))
    (execution : PairExecution D ViewData Rest)
    (presentation : ReturnReadout (NS b D Nat ViewData Nat Rest Body View) D ViewData Rest)
    (parameter : Parameter) (selection : Selected (NS b D Nat ViewData Nat Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value)
    (invocation : OriginalSourceEnvironment.Invocation (NS b D Nat ViewData Nat Rest Body View) View)
    (environment : Environment (Payload (NS b D Nat ViewData Nat Rest Body View) View))
    (openHistory : environment.replay = none)
    (entry : Judgment (localKernel (inputs baseInputs references) readout baseAdmissions original
      execution presentation parameter selection mode invocation) environment (enteredBody parameter))
    (state : Decoded (NS b D Nat ViewData Nat Rest Body View) View)
    (decoded : decode readout environment = some state) (active : state.activeRaw = some invocation)
    (packet : OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest) (actual : execution.Returns packet)
    (occurrence : Nat) (template : Event (NS b D Nat ViewData Nat Rest Body View))
    (old : PhiW (inputs baseInputs references) candidate (packetEvent template presentation packet))
    (cells : List (Option (Received Nat))) (vector : packet.world.cells = vectorStore cells)
    (represented : (returnState readout state environment parameter (presentation.outcome parameter packet) occurrence).installed =
      installed (packetEvent template presentation packet))
    (savedProviders : ∀ provider closure, template.current.providers provider = some closure →
      closure.savedEnvironment < packet.world.environments.size)
    (savedAliases : ∀ reference ∈ template.current.aliases, reference.environment < packet.world.environments.size)
    (node : Node Name D) (found : nodeAt packet.world.environments execution.capturedEnvironment = some node)
    (fields : EventFields b)
    (coherent : baseInputs.eventCoherent (bindEvent (packetEvent template presentation packet)
      execution.capturedEnvironment parameter.formal.name packet.value node found (selection.valueDescriptor mode) fields))
    (guards : (baseInputs.worldGuards (bindEvent (packetEvent template presentation packet)
      execution.capturedEnvironment parameter.formal.name packet.value node found (selection.valueDescriptor mode) fields)).Valid)
    (restrict : ∀ object : Installed (NS b D Nat ViewData Nat Rest Body View),
      object.Valid candidate (packetEvent template presentation packet) →
      object.Valid candidate (bindEvent (packetEvent template presentation packet)
        execution.capturedEnvironment parameter.formal.name packet.value node found (selection.valueDescriptor mode) fields))
    (returned : candidate (.value ⟨selection.valueDescriptor mode, presentation.assignment.value packet.value.value,
      presentation.assignment.root packet.value.value, bindEvent (packetEvent template presentation packet)
        execution.capturedEnvironment parameter.formal.name packet.value node found (selection.valueDescriptor mode) fields⟩)) :
    let after := environment.extend (returnBinder parameter)
      (scopeCandidate environment occurrence (.runtime (.returnRebind (presentation.outcome parameter packet))))
    ∃ delivered,
      decode readout (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) = some delivered ∧
      delivered.installed = installed (bindEvent (packetEvent template presentation packet)
        execution.capturedEnvironment parameter.formal.name packet.value node found (selection.valueDescriptor mode) fields) ∧
      PhiW (inputs baseInputs references) candidate (bindEvent (packetEvent template presentation packet)
        execution.capturedEnvironment parameter.formal.name packet.value node found (selection.valueDescriptor mode) fields) := by
  have consumer := entry_actual_return_consumer (inputs baseInputs references) readout baseAdmissions original
    execution presentation parameter selection mode invocation environment openHistory entry
  obtain ⟨witness, sharedOccurrence, decodedDelivery, _, _⟩ := consumer state decoded active packet actual occurrence
  refine ⟨_, decodedDelivery, ?_, ?_⟩
  · exact delivered_packet_registry readout _ template presentation parameter selection mode packet cells vector represented
      execution.capturedEnvironment node found fields witness _ sharedOccurrence
  · exact bind_phiW baseInputs references candidate (packetEvent template presentation packet) old cells vector
      savedProviders savedAliases execution.capturedEnvironment parameter.formal.name packet.value node found
      (selection.valueDescriptor mode) fields coherent guards restrict returned

end YulangClosure.OriginalFormalShared
