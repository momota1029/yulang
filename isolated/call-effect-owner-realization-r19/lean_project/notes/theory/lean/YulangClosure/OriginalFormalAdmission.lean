import YulangClosure.OriginalFormalShared
import YulangClosure.OriginalRetainedParameter

/-!
Source-owned formal declaration and logical proof packets at one actual Lambda
introduction. SG §3.3 distinguishes Desc values from ViewLogic/EventProof fields.
This local interpretation does not claim that the legacy flat admission API
can recover every occurrence route. No semantic membership is stored in a packet.
-/
namespace YulangClosure.OriginalFormalAdmission

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalParameterSemantics
open OriginalRetainedParameter OriginalFormalShared OriginalCheckingAdmission

variable {s : Sorts} {View : Type}

/-- A source constructor, its actual occurrence, and every typed predecessor.
The route is not a claim that the raw Site is globally fresh. -/
structure Introduction (s : Sorts) (View : Type) where
  parameter : Parameter
  route : Route
  telescope : Telescope s View parameter.typeScope

def Introduction.coordinate (intro : Introduction s View) : Coordinate :=
  intro.parameter.coordinate intro.route

def Introduction.selection (intro : Introduction s View) (assignment : FormalAssignment s View) :
    Selected s View intro.parameter :=
  select assignment intro.parameter intro.route intro.telescope.values

def readContract (state : Decoded s View) (point : Endpoint) : (entry : Entry) → Contract s entry
  | .value => state.assignment.descriptor point
  | .computation => state.interfaces point

def formalContract (state : Decoded s View) (parameter : Parameter) :
    Contract s parameter.formal.entry :=
  readContract state ⟨parameter.formal.site, .descriptor⟩ parameter.formal.entry

def declarationFor (state : Decoded s View) (point : Endpoint) :
    (entry : Entry) → Contract s entry → Logical s View
  | .value, descriptor =>
      ⟨[(point, descriptor)], [], state.viewMeaning, state.assignment.event.eta, state.assignment.event.witness⟩
  | .computation, interface =>
      ⟨[], [(point, interface)], state.viewMeaning, state.assignment.event.eta, state.assignment.event.witness⟩

def declaration (state : Decoded s View) (parameter : Parameter)
    (contract : Contract s parameter.formal.entry) : Logical s View :=
  declarationFor state ⟨parameter.formal.site, .descriptor⟩ parameter.formal.entry contract

def Introduction.description (intro : Introduction s View) (assignment : FormalAssignment s View)
    (state : Decoded s View) : Logical s View :=
  declaration state intro.parameter (intro.selection assignment).contract

/-- The declaration reference is a type index, not another editable contract.
All independent proof/assignment/view fields remain available. -/
structure ViewPacket (intro : Introduction s View) where
  viewMeaning : View → s.Interface
  eta : s.Assignment
  witness : s.JointWitness

def ViewPacket.reference {intro : Introduction s View} (_packet : ViewPacket intro) : Coordinate := intro.coordinate

def ViewPacket.encode {intro : Introduction s View} (packet : ViewPacket intro) : Logical s View :=
  ⟨[], [], packet.viewMeaning, packet.eta, packet.witness⟩

theorem view_reference_is_original (intro : Introduction s View) (packet : ViewPacket intro) :
    packet.reference = intro.parameter.coordinate intro.route := rfl

theorem view_has_no_desc_writes (intro : Introduction s View) (packet : ViewPacket intro) :
    packet.encode.descriptors = [] ∧ packet.encode.interfaces = [] := ⟨rfl, rfl⟩

theorem view_keeps_independent_proof_fields (intro : Introduction s View) (packet : ViewPacket intro) :
    packet.encode.viewMeaning = packet.viewMeaning ∧ packet.encode.eta = packet.eta ∧
      packet.encode.witness = packet.witness := ⟨rfl, rfl, rfl⟩

theorem declaration_selects (state : Decoded s View) (parameter : Parameter)
    (contract : Contract s parameter.formal.entry) :
    formalContract (state.logical (declaration state parameter contract)) parameter = contract := by
  suffices ∀ (entry : Entry) (value : Contract s entry),
      readContract (state.logical (declarationFor state ⟨parameter.formal.site, .descriptor⟩ entry value))
        ⟨parameter.formal.site, .descriptor⟩ entry = value from this _ _
  intro entry value
  cases entry <;> simp [readContract, declarationFor, Decoded.logical, put]

theorem view_preserves_contract (intro : Introduction s View) (packet : ViewPacket intro)
    (state : Decoded s View) (parameter : Parameter) :
    formalContract (state.logical packet.encode) parameter = formalContract state parameter := by
  suffices ∀ entry, readContract (state.logical packet.encode) ⟨parameter.formal.site, .descriptor⟩ entry =
      readContract state ⟨parameter.formal.site, .descriptor⟩ entry from this _
  intro entry
  cases entry <;> rfl

theorem view_preserves_actual_fields (intro : Introduction s View) (packet : ViewPacket intro)
    (state : Decoded s View) :
    (state.logical packet.encode).assignment.event.current = state.assignment.event.current ∧
    (state.logical packet.encode).assignment.event.history = state.assignment.event.history ∧
    (state.logical packet.encode).assignment.value = state.assignment.value ∧
    (state.logical packet.encode).assignment.root = state.assignment.root ∧
    (state.logical packet.encode).fixedFrames = state.fixedFrames := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem value_description_is_original_producer (intro : Introduction s View)
    (assignment : FormalAssignment s View) (readout : RuntimeReadout s View) (initial : Decoded s View)
    (mode : intro.parameter.formal.entry = .value) (actual : ActualEvent (Payload s View))
    (entryPath : List (EventStep (Payload s View))) :
    (formalDescriptionFrame readout initial assignment intro.parameter intro.route intro.telescope mode actual entryPath).value.data =
      .logical .description (intro.description assignment (replayTelescope readout initial intro.telescope)) := by
  rcases intro with ⟨⟨decl, ambient, context, site, ⟨formalSite, name, annotation, outer⟩, pattern, body⟩, route, telescope⟩
  cases outer <;> cases mode <;> rfl

theorem computation_description_is_original_producer (intro : Introduction s View)
    (assignment : FormalAssignment s View) (readout : RuntimeReadout s View) (initial : Decoded s View)
    (mode : intro.parameter.formal.entry = .computation) (actual : ActualEvent (Payload s View))
    (entryPath : List (EventStep (Payload s View))) :
    (interfaceDescriptionFrame readout initial assignment intro.parameter intro.route intro.telescope mode actual entryPath).value.data =
      .logical .description (intro.description assignment (replayTelescope readout initial intro.telescope)) := by
  rcases intro with ⟨⟨decl, ambient, context, site, ⟨formalSite, name, annotation, outer⟩, pattern, body⟩, route, telescope⟩
  cases outer <;> cases mode <;> rfl

/-- All nonlocal admissions retain their previous independent meanings.
The local choice recognizes a constructor, not a desired decoded equation. -/
def localAdmissions (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) : LocalAdmissions s View :=
  {base with logical := fun state binder kind data =>
    match kind with
    | .description =>
        if binder = descriptionBinder intro.parameter then data = intro.description assignment state
        else base.logical state binder kind data
    | .viewLogic =>
        if binder = viewBinder intro.parameter then ∃ packet : ViewPacket intro, data = packet.encode
        else base.logical state binder kind data
    | .publishedInstance | .eventProof => base.logical state binder kind data}

def localKernel (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (original : Kernel (Payload s View)) : Kernel (Payload s View) :=
  goalAdmissionKernel inputs readout (localAdmissions intro assignment base)
    (admissionKernel inputs readout (localAdmissions intro assignment base) original)

theorem local_actual_domains_unchanged (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) :
    (localAdmissions intro assignment base).receipt = base.receipt ∧
    (localAdmissions intro assignment base).returnRebind = base.returnRebind ∧
    (localAdmissions intro assignment base).response = base.response ∧
    (localAdmissions intro assignment base).rigidOperation = base.rigidOperation ∧
    (localAdmissions intro assignment base).oneShot = base.oneShot ∧
    (localAdmissions intro assignment base).shared = base.shared := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem event_proof_admission_unchanged (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) (state : Decoded s View) (binder : Binder) (data : Logical s View) :
    (localAdmissions intro assignment base).logical state binder .eventProof data ↔
      base.logical state binder .eventProof data := Iff.rfl

theorem produced_description_admitted (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (occurrence : Nat) :
    Admitted inputs readout (localAdmissions intro assignment base) environment
      (descriptionBinder intro.parameter)
      (scopeCandidate environment occurrence (.logical .description (intro.description assignment state))) := by
  apply (admitted_scoped_iff inputs readout _ environment _ state decoded occurrence _).mpr
  exact ⟨rfl, by simp [localAdmissions]⟩

theorem produced_view_admitted (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (occurrence : Nat) (packet : ViewPacket intro) :
    Admitted inputs readout (localAdmissions intro assignment base) environment
      (viewBinder intro.parameter) (scopeCandidate environment occurrence (.logical .viewLogic packet.encode)) := by
  apply (admitted_scoped_iff inputs readout _ environment _ state decoded occurrence _).mpr
  exact ⟨rfl, by simp only [localAdmissions]; exact ⟨packet, rfl⟩⟩

theorem admitted_description_is_produced (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout (localAdmissions intro assignment base) environment
      (descriptionBinder intro.parameter) candidate) :
    candidate.data = .logical .description (intro.description assignment state) := by
  obtain ⟨_, other, otherDecoded, valid⟩ := admitted
  have equal : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
  subst other
  cases payload : candidate.data with
  | root data => simp only [payload, DataAdmitted] at valid
  | shared data => simp [payload, DataAdmitted, descriptionBinder] at valid
  | runtime data => cases data <;> simp [payload, DataAdmitted, descriptionBinder] at valid
  | logical kind data =>
      cases kind <;> simp only [payload, DataAdmitted, LogicalKind.binderKind, descriptionBinder,
        reduceCtorEq, false_and] at valid
      simp only [localAdmissions, descriptionBinder, ↓reduceIte] at valid
      rw [valid.2]

theorem admitted_view_is_produced (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout (localAdmissions intro assignment base) environment
      (viewBinder intro.parameter) candidate) :
    ∃ packet : ViewPacket intro, candidate.data = .logical .viewLogic packet.encode := by
  obtain ⟨_, other, otherDecoded, valid⟩ := admitted
  have equal : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
  subst other
  cases payload : candidate.data with
  | root data => simp only [payload, DataAdmitted] at valid
  | shared data => simp [payload, DataAdmitted, viewBinder] at valid
  | runtime data => cases data <;> simp [payload, DataAdmitted, viewBinder] at valid
  | logical kind data =>
      cases kind <;> simp only [payload, DataAdmitted, LogicalKind.binderKind, viewBinder,
        reduceCtorEq, false_and] at valid
      simp only [localAdmissions, viewBinder, ↓reduceIte] at valid
      obtain ⟨packet, same⟩ := valid.2
      exact ⟨packet, by rw [same]⟩


theorem object_preserves_interfaces (state : Decoded s View) (entry : Endpoint × Object s) :
    (state.object entry).interfaces = state.interfaces := by
  rcases entry with ⟨point, value⟩
  cases value <;> rfl

theorem objects_preserve_interfaces (state : Decoded s View) (entries : List (Endpoint × Object s)) :
    (entries.foldl Decoded.object state).interfaces = state.interfaces := by
  induction entries generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, object_preserves_interfaces]

theorem runtime_preserves_contract (readout : RuntimeReadout s View) (state : Decoded s View)
    (binder : Binder) (data : Runtime s View) (parameter : Parameter) :
    formalContract (state.runtime readout binder data) parameter = formalContract state parameter := by
  suffices ∀ entry, readContract (state.runtime readout binder data) ⟨parameter.formal.site,.descriptor⟩ entry =
      readContract state ⟨parameter.formal.site,.descriptor⟩ entry from this _
  intro entry
  cases entry with
  | value => exact congrFun (runtime_preserves_descriptors readout state binder data) _
  | computation => exact congrFun (objects_preserve_interfaces state data.endpoints) _

theorem shared_preserves_contract (state : Decoded s View) (data : Shared s) (parameter : Parameter) :
    formalContract (state.shared data) parameter = formalContract state parameter := rfl

theorem event_admission_is_runtime (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (state : Decoded s View) (binder : Binder)
    (event : binder.isEvent = true) (payload : Payload s View)
    (valid : DataAdmitted inputs readout admissions state binder payload) :
    ∃ data : Runtime s View, payload = .runtime data := by
  cases payload with
  | runtime data => exact ⟨data,rfl⟩
  | root data => exact False.elim valid
  | shared data =>
      have absent : binder.isEvent = false := by
        unfold Binder.isEvent
        rw [valid.1]
      rw [absent] at event
      cases event
  | logical kind data =>
      have absent : binder.isEvent = false := by
        unfold Binder.isEvent
        rw [← valid.1]
        cases kind <;> rfl
      rw [absent] at event
      cases event

theorem admitted_event_preserves_contract (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (binder : Binder) (event : binder.isEvent = true) (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions environment binder candidate) (parameter : Parameter) :
    ∃ after, decode readout (environment.extend binder candidate) = some after ∧
      formalContract after parameter = formalContract state parameter := by
  obtain ⟨_, other, otherDecoded, valid⟩ := admitted
  have equal : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
  subst other
  obtain ⟨data, payload⟩ := event_admission_is_runtime inputs readout admissions state binder event candidate.data valid
  refine ⟨_, decode_extend readout environment binder candidate state decoded, ?_⟩
  simp only [decodeFrame, payload, Decoded.retain]
  exact runtime_preserves_contract readout state binder data parameter

theorem admitted_shared_preserves_contract (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (parameter : Parameter) (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions environment (sharedBinder parameter) candidate) :
    ∃ after, decode readout (environment.extend (sharedBinder parameter) candidate) = some after ∧
      formalContract after parameter = formalContract state parameter := by
  obtain ⟨_, other, otherDecoded, valid⟩ := admitted
  have equal : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
  subst other
  cases payload : candidate.data with
  | root data => simp only [payload,DataAdmitted] at valid
  | logical kind data => cases kind <;> simp [payload,DataAdmitted,LogicalKind.binderKind,sharedBinder] at valid
  | runtime data => cases data <;> simp [payload,DataAdmitted,sharedBinder] at valid
  | shared data =>
      refine ⟨_,decode_extend readout environment _ candidate state decoded,?_⟩
      simp only [decodeFrame,payload,Decoded.retain]
      rfl

/-- Actual Build inversion at this source introduction. The selected contract
is computed from its whole prior telescope; no endpoint equality is an input. -/
theorem actual_build_selects_formal (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (annotation : Option Declaration)
    (solves : Satisfies (localKernel intro assignment inputs readout base original) environment
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite,annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body))) :
    let kernel := localKernel intro assignment inputs readout base original
    ∃ description view packet,
      description.data = .logical .description (intro.description assignment state) ∧
      view.data = .logical .viewLogic (ViewPacket.encode (intro := intro) packet) ∧
      kernel.admitted environment (descriptionBinder intro.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder intro.parameter) description)
        (viewBinder intro.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view)
        (invocationBinder intro.parameter) invocation →
      ∃ receipt after,
        kernel.admitted
          (((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
             (invocationBinder intro.parameter) invocation) (receiptBinder intro.parameter) receipt ∧
        decode readout
          ((((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
             (invocationBinder intro.parameter) invocation).extend (receiptBinder intro.parameter) receipt) = some after ∧
        formalContract after intro.parameter = (intro.selection assignment).contract ∧
        Judgment kernel
          ((((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
             (invocationBinder intro.parameter) invocation).extend (receiptBinder intro.parameter) receipt)
          (enteredBody intro.parameter) := by
  obtain ⟨description, descValid, view, viewValid, every⟩ :=
    build_entry _ environment intro.parameter annotation solves
  have descPayload := admitted_description_is_produced intro assignment inputs readout base environment state decoded description descValid
  have descDecoded := decode_extend readout environment (descriptionBinder intro.parameter) description state decoded
  simp only [decodeFrame,descPayload] at descDecoded
  obtain ⟨packet,viewPayload⟩ := admitted_view_is_produced intro assignment inputs readout base _ _ descDecoded view viewValid
  have viewDecoded := decode_extend readout _ (viewBinder intro.parameter) view _ descDecoded
  simp only [decodeFrame,viewPayload] at viewDecoded
  have selected : formalContract ((state.logical (intro.description assignment state)).logical packet.encode) intro.parameter =
      (intro.selection assignment).contract :=
    (view_preserves_contract intro packet _ _).trans (declaration_selects state intro.parameter _)
  refine ⟨description,view,packet,descPayload,viewPayload,descValid,viewValid,?_⟩
  intro invocation invocationValid
  obtain ⟨receipt,receiptValid,entry⟩ := every invocation invocationValid
  obtain ⟨invoked,invokedDecoded,kept⟩ := admitted_event_preserves_contract inputs readout
    (localAdmissions intro assignment base) _ _ viewDecoded (invocationBinder intro.parameter) rfl invocation invocationValid intro.parameter
  obtain ⟨after,afterDecoded,keptAgain⟩ := admitted_event_preserves_contract inputs readout
    (localAdmissions intro assignment base) _ invoked invokedDecoded (receiptBinder intro.parameter) rfl receipt receiptValid intro.parameter
  exact ⟨receipt,after,receiptValid,afterDecoded,keptAgain.trans (kept.trans selected),entry⟩


/-- A prior environment assembled from the exact typed telescope. No existing
environment is reset; every source/runtime metadata field is an independent input. -/
structure Prior (s : Sorts) (View : Type) where
  root : Root s View
  anchors : AnchorKey (Payload s View) → ScopedValue (Payload s View)
  publications : PublicationId (Payload s View) → Option (PublicationRecord (Payload s View))
  eventPath : List (EventStep (Payload s View))
  names : List (Name × PublicationId (Payload s View))
  replay : Option (List (Frame (Payload s View)))
  initializers : List (InitializerEntry (Payload s View))

def priorEnvironment (intro : Introduction s View) (prior : Prior s View) : Environment (Payload s View) :=
  ⟨.root prior.root,prior.anchors,prior.publications,intro.parameter.declaration,prior.eventPath,
    prior.names,intro.telescope.frames,prior.replay,prior.initializers⟩

theorem prior_decodes_whole_telescope (intro : Introduction s View) (prior : Prior s View)
    (readout : RuntimeReadout s View) :
    decode readout (priorEnvironment intro prior) =
      some (replayTelescope readout prior.root.decoded intro.telescope) := rfl

theorem prior_keeps_full_metadata (intro : Introduction s View) (prior : Prior s View) :
    (priorEnvironment intro prior).frames = intro.telescope.frames ∧
    (priorEnvironment intro prior).eventPath = prior.eventPath ∧
    (priorEnvironment intro prior).names = prior.names ∧
    (priorEnvironment intro prior).replay = prior.replay ∧
    (priorEnvironment intro prior).anchors = prior.anchors ∧
    (priorEnvironment intro prior).publications = prior.publications := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem value_entry_body_keeps_contract (inputs : Inputs s) (readout : RuntimeReadout s View)
    (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (parameter : Parameter) (mode : parameter.formal.entry = .value)
    (environment : Environment (Payload s View)) (openHistory : environment.replay = none)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (entry : Judgment (localKernel intro assignment inputs readout base original) environment (enteredBody parameter))
    (returned : ScopedValue (Payload s View))
    (valid : Admitted inputs readout (localAdmissions intro assignment base) environment (returnBinder parameter) returned) :
    let afterReturn := environment.extend (returnBinder parameter) returned
    let afterShared := afterReturn.extend (sharedBinder parameter) (afterReturn.anchorValue (sharedBinder parameter))
    ∃ after, decode readout afterShared = some after ∧
      formalContract after parameter = formalContract state parameter ∧
      Judgment (localKernel intro assignment inputs readout base original) afterShared (checkedBody parameter) := by
  obtain ⟨shared,body⟩ := value_entry_shared _ environment parameter mode openHistory entry returned valid
  obtain ⟨returnedState,returnedDecoded,first⟩ := admitted_event_preserves_contract inputs readout (localAdmissions intro assignment base)
    environment state decoded (returnBinder parameter) rfl returned valid parameter
  obtain ⟨after,afterDecoded,second⟩ := admitted_shared_preserves_contract inputs readout (localAdmissions intro assignment base)
    _ returnedState returnedDecoded parameter _ shared
  exact ⟨after,afterDecoded,second.trans first,body⟩

theorem computation_entry_body_keeps_contract (inputs : Inputs s) (readout : RuntimeReadout s View)
    (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (parameter : Parameter) (mode : parameter.formal.entry = .computation)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (entry : Judgment (localKernel intro assignment inputs readout base original) environment (enteredBody parameter)) :
    let afterShared := environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter))
    ∃ after, decode readout afterShared = some after ∧
      formalContract after parameter = formalContract state parameter ∧
      Judgment (localKernel intro assignment inputs readout base original) afterShared (checkedBody parameter) := by
  obtain ⟨shared,body⟩ := computation_entry_shared _ environment parameter mode entry
  obtain ⟨after,afterDecoded,kept⟩ := admitted_shared_preserves_contract inputs readout (localAdmissions intro assignment base)
    environment state decoded parameter _ shared
  exact ⟨after,afterDecoded,kept,body⟩

theorem view_rejects_descriptor_overwrite (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) (state : Decoded s View) (data : Logical s View)
    (writes : data.descriptors ≠ []) :
    ¬ (localAdmissions intro assignment base).logical state (viewBinder intro.parameter) .viewLogic data := by
  intro valid
  change (if viewBinder intro.parameter = viewBinder intro.parameter then _ else _) at valid
  simp only at valid
  obtain ⟨packet,same⟩ := valid
  exact writes (congrArg Logical.descriptors same)

theorem view_rejects_interface_overwrite (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) (state : Decoded s View) (data : Logical s View)
    (writes : data.interfaces ≠ []) :
    ¬ (localAdmissions intro assignment base).logical state (viewBinder intro.parameter) .viewLogic data := by
  intro valid
  change (if viewBinder intro.parameter = viewBinder intro.parameter then _ else _) at valid
  simp only at valid
  obtain ⟨packet,same⟩ := valid
  exact writes (congrArg Logical.interfaces same)

theorem distinct_incoming_contracts_stay_distinct (intro : Introduction s View)
    (first second : FormalAssignment s View) (state : Decoded s View)
    (different : (intro.selection first).contract ≠ (intro.selection second).contract) :
    intro.description first state ≠ intro.description second state := by
  intro same
  have equality := congrArg (fun data => formalContract (state.logical data) intro.parameter) same
  simp only [Introduction.description, declaration_selects] at equality
  exact different equality

/-- Actual occurrence routes survive in the owner packet, while the legacy
binder passed to LocalAdmissions does not contain them. This is an interface
discriminator, not a claim that both records are admitted native histories. -/
theorem distinct_routes_same_flat_binder (intro : Introduction s View) (other : Route)
    (different : intro.route ≠ other) :
    intro.coordinate ≠ ({intro with route := other} : Introduction s View).coordinate ∧
    descriptionBinder intro.parameter = descriptionBinder ({intro with route := other} : Introduction s View).parameter ∧
    viewBinder intro.parameter = viewBinder ({intro with route := other} : Introduction s View).parameter := by
  refine ⟨?_,rfl,rfl⟩
  intro same
  exact different (congrArg Coordinate.introduction same)

theorem no_erased_owner_singleton_admission (state : Decoded s View) (parameter : Parameter)
    (first second : Contract s parameter.formal.entry) (different : first ≠ second) :
    ¬ ∃ admits : Logical s View → Prop,
      (∀ data, admits data ↔ data = declaration state parameter first) ∧
      (∀ data, admits data ↔ data = declaration state parameter second) := by
  rintro ⟨admits,left,right⟩
  have chosen := (left (declaration state parameter first)).mpr rfl
  have same := (right (declaration state parameter first)).mp chosen
  have equality := congrArg (fun data => formalContract (state.logical data) parameter) same
  rw [declaration_selects, declaration_selects] at equality
  exact different equality

theorem actual_build_from_whole_telescope (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (prior : Prior s View)
    (annotation : Option Declaration)
    (solves : Satisfies (localKernel intro assignment inputs readout base original) (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite,annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body))) :
    let environment := priorEnvironment intro prior
    let state := replayTelescope readout prior.root.decoded intro.telescope
    let kernel := localKernel intro assignment inputs readout base original
    ∃ description view packet,
      description.data = .logical .description (intro.description assignment state) ∧
      view.data = .logical .viewLogic (ViewPacket.encode (intro := intro) packet) ∧
      kernel.admitted environment (descriptionBinder intro.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder intro.parameter) description)
        (viewBinder intro.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view)
        (invocationBinder intro.parameter) invocation →
      ∃ receipt after,
        kernel.admitted
          (((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
             (invocationBinder intro.parameter) invocation) (receiptBinder intro.parameter) receipt ∧
        decode readout
          ((((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
             (invocationBinder intro.parameter) invocation).extend (receiptBinder intro.parameter) receipt) = some after ∧
        formalContract after intro.parameter = (intro.selection assignment).contract ∧
        Judgment kernel
          ((((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
             (invocationBinder intro.parameter) invocation).extend (receiptBinder intro.parameter) receipt)
          (enteredBody intro.parameter) := by
  exact actual_build_selects_formal intro assignment inputs readout base original
    (priorEnvironment intro prior) (replayTelescope readout prior.root.decoded intro.telescope)
    (prior_decodes_whole_telescope intro prior readout) annotation solves



theorem runtime_admission_unchanged (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    DataAdmitted inputs readout (localAdmissions intro assignment base) state binder (.runtime data) ↔
      DataAdmitted inputs readout base state binder (.runtime data) := by
  cases data <;> exact Iff.rfl

theorem checking_runtime_admission_unchanged (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (state : Decoded s View) (goal : CheckGoal) (binder : Binder) (data : Runtime s View) :
    GoalDataAdmitted inputs readout (localAdmissions intro assignment base) state goal binder (.runtime data) ↔
      GoalDataAdmitted inputs readout base state goal binder (.runtime data) := by
  cases data <;> exact Iff.rfl

theorem description_and_view_keep_raw_identity (intro : Introduction s View)
    (environment : Environment (Payload s View)) (description view : ScopedValue (Payload s View)) :
    let after := (environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view
    after.eventPath = environment.eventPath ∧ after.anchors = environment.anchors ∧
      after.publications = environment.publications ∧ after.origin = environment.origin := ⟨rfl,rfl,rfl,rfl⟩

end YulangClosure.OriginalFormalAdmission
