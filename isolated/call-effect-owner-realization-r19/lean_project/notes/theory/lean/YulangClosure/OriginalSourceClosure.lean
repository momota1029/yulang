import YulangClosure.OriginalFormalAdmission

/-!
Original body EventProof ownership and its finite body-consumer check.

SG §3.3 assigns EventProof its description-owned evidence at the actual
event. It does not introduce another Desc or replace installed runtime
fields. This module constructs that packet, recovers its actual source owner,
and uses the existing finite Checking proof at the original body consumer.
The original body and pattern remain arbitrary source trees.
-/
namespace YulangClosure.OriginalSourceClosure

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalFormalShared
open OriginalFormalAdmission OriginalCheckingAdmission OriginalSourceChecking

variable {s : Sorts} {View : Type}

def bodyProofBinder (parameter : Parameter) : Binder :=
  ⟨parameter.body.site, .eventProof, 0⟩

def bodyGoal (parameter : Parameter) : CheckGoal :=
  ⟨.computation, parameter.body.site, OriginalFormalShared.bodyContext parameter,
    ⟨parameter.body.site, .finalRoot⟩, ⟨parameter.lambdaSite, .bodyConsumer⟩⟩

/-- The owner is computed from the actual checkedBody occurrence. The
original prior telescope remains an input, not an empty-scope replacement. -/
def bodyProofOwner (parameter : Parameter) (route : Route)
    (scope : List ScopeEntry) : Owner :=
  owner (route ++ [0, 1]) scope (bodyProofBinder parameter) .descriptionProof

theorem body_proof_owner_registered (parameter : Parameter) (route : Route)
    (scope : List ScopeEntry) :
    bodyProofOwner parameter route scope ∈
      owners route scope (checkedBody parameter) := by
  simp [bodyProofOwner, checkedBody, owners, forestOwners, RuleForest.two,
    RuleForest.one, binderOwner, bodyProofBinder, Binder.isEvent,
    List.append_assoc]

/-- Every independent logical assignment, witness and view interpretation
is retained. The original owner is an index; no runtime key stores it. -/
structure EventProofPacket (s : Sorts) (View : Type) (introduction : Owner) where
  viewMeaning : View → s.Interface
  eta : s.Assignment
  witness : s.JointWitness

def EventProofPacket.encode {introduction : Owner}
    (packet : EventProofPacket s View introduction) : Logical s View :=
  ⟨[], [], packet.viewMeaning, packet.eta, packet.witness⟩

/-- All original independent checks of the proof fields remain. Only the
EventProof constructor is made explicit; other logical kinds are unchanged.
The packet grammar is owner-uniform and therefore needs no flat-Site lookup
to choose a formal descriptor or a route-specific assignment. -/
def proofAdmissions (base : LocalAdmissions s View) : LocalAdmissions s View :=
  {base with logical := fun state binder kind data =>
    base.logical state binder kind data ∧
      (kind = .eventProof → data.descriptors = [] ∧ data.interfaces = [])}

theorem other_logical_admission_unchanged (base : LocalAdmissions s View)
    (state : Decoded s View) (binder : Binder) (kind : LogicalKind)
    (different : kind ≠ .eventProof) (data : Logical s View) :
    (proofAdmissions base).logical state binder kind data ↔
      base.logical state binder kind data := by
  simp only [proofAdmissions, different, false_implies, and_true]

theorem runtime_admission_unchanged (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (state : Decoded s View) (binder : Binder)
    (data : Runtime s View) :
    DataAdmitted inputs readout (proofAdmissions base) state binder (.runtime data) ↔
      DataAdmitted inputs readout base state binder (.runtime data) := by
  cases data <;> exact Iff.rfl

theorem checking_runtime_admission_unchanged (inputs : Inputs s)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (state : Decoded s View) (goal : CheckGoal) (binder : Binder)
    (data : Runtime s View) :
    GoalDataAdmitted inputs readout (proofAdmissions base) state goal binder (.runtime data) ↔
      GoalDataAdmitted inputs readout base state goal binder (.runtime data) := by
  cases data <;> exact Iff.rfl

theorem proof_packet_admission_exact (base : LocalAdmissions s View)
    (state : Decoded s View) (introduction : Owner)
    (packet : EventProofPacket s View introduction) :
    (proofAdmissions base).logical state introduction.binder .eventProof packet.encode ↔
      base.logical state introduction.binder .eventProof packet.encode := by
  simp [proofAdmissions, EventProofPacket.encode]

/-- Inverting admitted raw data constructs the packet; preservation is not
assumed as a semantic law or as an endpoint readback equation. -/
theorem admitted_proof_packet (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (environment : Environment (Payload s View))
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (introduction : Owner) (kind : introduction.binder.kind = .eventProof)
    (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout (proofAdmissions base)
      environment introduction.binder candidate) :
    ∃ packet : EventProofPacket s View introduction,
      candidate.data = .logical .eventProof packet.encode ∧
      base.logical state introduction.binder .eventProof packet.encode := by
  obtain ⟨_, other, found, valid⟩ := admitted
  have same := Option.some.inj (found.symm.trans decoded)
  subst other
  cases payload : candidate.data with
  | root data => simp only [payload, DataAdmitted] at valid
  | shared data => simp [payload, DataAdmitted, kind] at valid
  | runtime data => cases data <;> simp [payload, DataAdmitted, kind] at valid
  | logical logical data =>
      cases logical <;>
        simp only [payload, DataAdmitted, LogicalKind.binderKind, kind,
          reduceCtorEq, false_and] at valid
      obtain ⟨original, fields⟩ := valid.2
      obtain ⟨descriptors, interfaces⟩ := fields rfl
      let packet : EventProofPacket s View introduction :=
        ⟨data.viewMeaning, data.eta, data.witness⟩
      have dataEq : data = packet.encode := by
        cases data
        simp_all [packet, EventProofPacket.encode]
      exact ⟨packet, by rw [dataEq], by simpa only [dataEq] using original⟩

/-- The allowed logical changes are exactly exposed: eta/witness/views may
vary. Descriptions, interfaces, installed certificates and actual execution
fields are preserved by the ordinary decoder itself. -/
theorem proof_packet_preserves (state : Decoded s View) (introduction : Owner)
    (packet : EventProofPacket s View introduction) :
    (state.logical packet.encode).assignment.descriptor = state.assignment.descriptor ∧
    (state.logical packet.encode).interfaces = state.interfaces ∧
    (state.logical packet.encode).installed = state.installed ∧
    (state.logical packet.encode).assignment.value = state.assignment.value ∧
    (state.logical packet.encode).assignment.root = state.assignment.root ∧
    (state.logical packet.encode).assignment.binding = state.assignment.binding ∧
    (state.logical packet.encode).assignment.event.fiber = state.assignment.event.fiber ∧
    (state.logical packet.encode).assignment.event.eta0 = state.assignment.event.eta0 ∧
    (state.logical packet.encode).assignment.event.history = state.assignment.event.history ∧
    (state.logical packet.encode).assignment.event.current = state.assignment.event.current ∧
    (state.logical packet.encode).assignment.event.scope = state.assignment.event.scope ∧
    (state.logical packet.encode).assignment.event.authority = state.assignment.event.authority ∧
    (state.logical packet.encode).assignment.event.incidence = state.assignment.event.incidence ∧
    (state.logical packet.encode).assignment.event.dictionary = state.assignment.event.dictionary ∧
    (state.logical packet.encode).fixedFrames = state.fixedFrames ∧
    (state.logical packet.encode).callOwners = state.callOwners ∧
    (state.logical packet.encode).active = state.active ∧
    (state.logical packet.encode).activeRaw = state.activeRaw := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem proof_packet_keeps_formal (state : Decoded s View) (introduction : Owner)
    (packet : EventProofPacket s View introduction) (parameter : Parameter) :
    formalContract (state.logical packet.encode) parameter = formalContract state parameter := by
  unfold formalContract
  cases parameter.formal.entry <;> rfl

theorem proof_packet_uses_current_evidence (state : Decoded s View)
    (introduction : Owner) (packet : EventProofPacket s View introduction) :
    (state.logical packet.encode).assignment.event.eta = packet.eta ∧
    (state.logical packet.encode).assignment.event.witness = packet.witness ∧
    (state.logical packet.encode).viewMeaning = packet.viewMeaning := ⟨rfl, rfl, rfl⟩

theorem body_proof_keeps_actual_identity (environment : Environment (Payload s View))
    (parameter : Parameter) (candidate : ScopedValue (Payload s View)) :
    (environment.extend (bodyProofBinder parameter) candidate).eventPath = environment.eventPath ∧
    (environment.extend (bodyProofBinder parameter) candidate).anchors = environment.anchors ∧
    (environment.extend (bodyProofBinder parameter) candidate).publications = environment.publications ∧
    (environment.extend (bodyProofBinder parameter) candidate).origin = environment.origin ∧
    (environment.extend (bodyProofBinder parameter) candidate).replay = environment.replay :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def closureAdmissions (intro : Introduction s View) (assignment : FormalAssignment s View)
    (base : LocalAdmissions s View) : LocalAdmissions s View :=
  OriginalFormalAdmission.localAdmissions intro assignment (proofAdmissions base)

theorem closure_proof_admission (intro : Introduction s View)
    (assignment : FormalAssignment s View) (base : LocalAdmissions s View)
    (state : Decoded s View) (binder : Binder) (data : Logical s View) :
    (closureAdmissions intro assignment base).logical state binder .eventProof data ↔
      (proofAdmissions base).logical state binder .eventProof data := Iff.rfl

def closureKernel (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) : Kernel (Payload s View) :=
  OriginalSourceChecking.kernel inputs registry declarations (environmentReading inputs readout ports)
    (OriginalFormalAdmission.localKernel intro assignment inputs readout (proofAdmissions base) original)

/-- Checking captures the final goal-specific admission, after both source
logical constructors have been installed. -/
theorem closure_kernel_is_local (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View)) :
    OriginalFormalAdmission.localKernel intro assignment inputs readout (proofAdmissions base)
      (closureKernel intro assignment inputs registry declarations readout base ports original) =
      closureKernel intro assignment inputs registry declarations readout base ports original := rfl

theorem closure_admitted_proof_iff (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (kind : binder.kind = .eventProof) (candidate : ScopedValue (Payload s View)) :
    Admitted inputs readout (closureAdmissions intro assignment base) environment binder candidate ↔
      Admitted inputs readout (proofAdmissions base) environment binder candidate := by
  have data : ∀ state payload,
      DataAdmitted inputs readout (closureAdmissions intro assignment base) state binder payload ↔
        DataAdmitted inputs readout (proofAdmissions base) state binder payload := by
    intro state payload
    cases payload with
    | root data => exact Iff.rfl
    | shared data => exact Iff.rfl
    | runtime data => cases data <;> exact Iff.rfl
    | logical logical data =>
        cases logical <;>
          simp [DataAdmitted, LogicalKind.binderKind, kind,
            closureAdmissions, OriginalFormalAdmission.localAdmissions]
  simp only [Admitted, data]

/-- The actual generated body contains both its arbitrary original pattern
and its original computation check. The EventProof existential supplies the
packet in the SAME environment used by the body and the consumer check.
The semantic action below is derived by the existing full finite Checking
recursion; it is not a supplied body-soundness premise. -/
theorem checked_body_consumer (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (route : Route) (scope : List ScopeEntry)
    (derivation : Judgment
      (closureKernel intro assignment inputs registry declarations readout base ports original)
      environment (checkedBody intro.parameter)) :
    ∃ (candidate : ScopedValue (Payload s View))
      (packet : EventProofPacket s View (bodyProofOwner intro.parameter route scope)),
      candidate.data = .logical .eventProof packet.encode ∧
      decode readout (environment.extend (bodyProofBinder intro.parameter) candidate) =
        some (state.logical packet.encode) ∧
      formalContract (state.logical packet.encode) intro.parameter = formalContract state intro.parameter ∧
      SourceJudgment (closureKernel intro assignment inputs registry declarations readout base ports original)
        environment (OriginalFormalShared.formalContext intro.parameter) intro.parameter.pattern ∧
      Checking (closureKernel intro assignment inputs registry declarations readout base ports original)
        (environment.extend (bodyProofBinder intro.parameter) candidate) (bodyGoal intro.parameter) ∧
      SourceJudgment (closureKernel intro assignment inputs registry declarations readout base ports original)
        (environment.extend (bodyProofBinder intro.parameter) candidate)
        (OriginalFormalShared.bodyContext intro.parameter) intro.parameter.body ∧
      ∀ raw : RawObservation s,
        Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.body.site, .finalRoot⟩))) →
        Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.lambdaSite, .bodyConsumer⟩))) := by
  cases derivation with
  | rule _ children =>
      cases children with
      | cons pattern rest =>
          cases rest with
          | cons proof _ =>
              cases proof with
              | existsE candidate admitted body =>
                  have localAdmitted : Admitted inputs readout (proofAdmissions base)
                      environment (bodyProofBinder intro.parameter) candidate :=
                    (closure_admitted_proof_iff intro assignment inputs readout base environment
                      (bodyProofBinder intro.parameter) rfl candidate).mp admitted
                  obtain ⟨packet, payload, _⟩ := admitted_proof_packet inputs readout base
                    environment state decoded (bodyProofOwner intro.parameter route scope) rfl
                    candidate localAdmitted
                  have nextDecoded := decode_extend readout environment
                    (bodyProofBinder intro.parameter) candidate state decoded
                  simp only [decodeFrame, payload] at nextDecoded
                  cases body with
                  | rule locals bodies =>
                      have consumer := locals (.checking (bodyGoal intro.parameter))
                        (List.mem_append.mpr (Or.inr List.mem_cons_self))
                      cases consumer with
                      | checking consumer =>
                          cases bodies with
                          | cons source _ =>
                              refine ⟨candidate, packet, payload, nextDecoded,
                                proof_packet_keeps_formal state _ packet intro.parameter,
                                pattern, consumer, source, ?_⟩
                              intro raw
                              have semantic := checking_sound inputs registry declarations
                                (environmentReading inputs readout ports)
                                (OriginalFormalAdmission.localKernel intro assignment inputs readout
                                  (proofAdmissions base) original) consumer
                              exact computation_action inputs readout ports _ _ nextDecoded
                                (bodyGoal intro.parameter) rfl semantic raw

def lambdaBodyRoute (parameter : Parameter) : Route :=
  parameter.registration.physicalRetainedOwner.route ++ [0]

def lambdaBodyScope (parameter : Parameter) : List ScopeEntry :=
  extendScope parameter.registration.physicalRetainedOwner.telescope
    parameter.registration.physicalRetainedOwner.route (sharedBinder parameter)

/-- The body proof owner occurs in the actual raw Lambda traversal, for
either entry mode and arbitrary source pattern/body. -/
theorem actual_lambda_body_owner (parameter : Parameter) :
    bodyProofOwner parameter (lambdaBodyRoute parameter) (lambdaBodyScope parameter) ∈
      sourceOwners parameter.context parameter.source := by
  unfold sourceOwners
  rw [actual_lambda_tree]
  cases mode : parameter.formal.entry <;>
    simp [lambdaTree, enteredBody, retainedBody, checkedBody, owners, forestOwners,
      RuleForest.one, RuleForest.two, binderOwner, Binder.isEvent,
      bodyProofOwner, bodyProofBinder, lambdaBodyRoute, lambdaBodyScope,
      Parameter.registration, lambdaEntry, lambdaScope, EntryRegistration.physicalRetainedOwner,
      EntryRegistration.retainedOwner, owner, extendScope, descriptionBinder,
      viewBinder, invocationBinder, receiptBinder, sharedBinder, returnBinder,
      mode]

def scopedBodyRoute (intro : Introduction s View) : Route :=
  intro.route ++ lambdaBodyRoute intro.parameter

def scopedBodyScope (intro : Introduction s View) : List ScopeEntry :=
  intro.parameter.ambient ++ (lambdaBodyScope intro.parameter).map
    (fun entry => {entry with route := intro.route ++ entry.route})

/-- The original enclosing route and every ambient typed predecessor are
retained, including when sites repeat. No global freshness premise is used. -/
theorem scoped_body_owner_registered (intro : Introduction s View) :
    bodyProofOwner intro.parameter (scopedBodyRoute intro) (scopedBodyScope intro) ∈
      owners intro.route intro.parameter.ambient (sourceRules intro.parameter.context intro.parameter.source) := by
  rw [actual_lambda_tree]
  cases mode : intro.parameter.formal.entry <;>
    simp [lambdaTree, enteredBody, retainedBody, checkedBody, owners, forestOwners,
      RuleForest.one, RuleForest.two, binderOwner, Binder.isEvent,
      bodyProofOwner, bodyProofBinder, scopedBodyRoute, scopedBodyScope,
      lambdaBodyRoute, lambdaBodyScope, Parameter.registration, lambdaEntry, lambdaScope,
      EntryRegistration.physicalRetainedOwner, EntryRegistration.retainedOwner,
      owner, extendScope, descriptionBinder, viewBinder, invocationBinder,
      receiptBinder, sharedBinder, returnBinder, mode, List.append_assoc]

theorem body_owner_keeps_ambient (intro : Introduction s View) (entry : ScopeEntry)
    (earlier : entry ∈ intro.parameter.ambient) :
    entry ∈ (bodyProofOwner intro.parameter (scopedBodyRoute intro) (scopedBodyScope intro)).telescope :=
  List.mem_append_left _ earlier

/-- This is an OUTPUT property of the actual body scope, never a Kernel
field or an admission condition. The computed contract, source pattern,
source body, original Checking derivation and complete raw action coexist
under the same actual EventProof witness. -/
def BodyConsumer (intro : Introduction s View) (assignment : FormalAssignment s View)
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View)) : Prop :=
  ∃ (state : Decoded s View) (candidate : ScopedValue (Payload s View))
    (packet : EventProofPacket s View (bodyProofOwner intro.parameter
      (scopedBodyRoute intro) (scopedBodyScope intro))),
    decode readout environment = some state ∧
    candidate.data = .logical .eventProof packet.encode ∧
    decode readout (environment.extend (bodyProofBinder intro.parameter) candidate) =
      some (state.logical packet.encode) ∧
    formalContract (state.logical packet.encode) intro.parameter = (intro.selection assignment).contract ∧
    SourceJudgment (closureKernel intro assignment inputs registry declarations readout base ports original)
      environment (OriginalFormalShared.formalContext intro.parameter) intro.parameter.pattern ∧
    Checking (closureKernel intro assignment inputs registry declarations readout base ports original)
      (environment.extend (bodyProofBinder intro.parameter) candidate) (bodyGoal intro.parameter) ∧
    SourceJudgment (closureKernel intro assignment inputs registry declarations readout base ports original)
      (environment.extend (bodyProofBinder intro.parameter) candidate)
      (OriginalFormalShared.bodyContext intro.parameter) intro.parameter.body ∧
    ∀ raw : RawObservation s,
      Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.body.site, .finalRoot⟩))) →
      Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.lambdaSite, .bodyConsumer⟩)))

private theorem body_consumer_of_checked_body (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (selected : formalContract state intro.parameter = (intro.selection assignment).contract)
    (body : Judgment
      (closureKernel intro assignment inputs registry declarations readout base ports original)
      environment (checkedBody intro.parameter)) :
    BodyConsumer intro assignment inputs registry declarations readout base ports original environment := by
  obtain ⟨candidate, packet, payload, nextDecoded, preserved, pattern, consumer, source, action⟩ :=
    checked_body_consumer intro assignment inputs registry declarations readout base ports original
      environment state decoded (scopedBodyRoute intro) (scopedBodyScope intro) body
  exact ⟨state, candidate, packet, decoded, payload, nextDecoded, preserved.trans selected,
    pattern, consumer, source, action⟩

def receivedEnvironment (environment : Environment (Payload s View)) (parameter : Parameter)
    (description view invocation receipt : ScopedValue (Payload s View)) : Environment (Payload s View) :=
  (((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend
    (invocationBinder parameter) invocation).extend (receiptBinder parameter) receipt

def retainedEnvironment (environment : Environment (Payload s View)) (parameter : Parameter) :
    Environment (Payload s View) :=
  environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter))

/-- Actual original Value-entry Build to its body consumer. No chosen formal
contract, entry/body derivation, EventProof packet, descriptor-preservation
law, or body computation action is an input. The universal Return domain
and all arbitrary source pattern/body constructors are retained. -/
theorem generated_value_body_consumer (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (prior : Prior s View) (annotation : Option Declaration)
    (mode : intro.parameter.formal.entry = .value)
    (solves : Satisfies
      (closureKernel intro assignment inputs registry declarations readout base ports original)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body))) :
    let kernel := closureKernel intro assignment inputs registry declarations readout base ports original
    let environment := priorEnvironment intro prior
    ∃ description view,
      kernel.admitted environment (descriptionBinder intro.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder intro.parameter) description)
        (viewBinder intro.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view)
        (invocationBinder intro.parameter) invocation →
      ∃ receipt,
        kernel.admitted
          (((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
            (invocationBinder intro.parameter) invocation) (receiptBinder intro.parameter) receipt ∧
        ∀ returned, kernel.admitted (receivedEnvironment environment intro.parameter description view invocation receipt)
          (returnBinder intro.parameter) returned →
          BodyConsumer intro assignment inputs registry declarations readout base ports original
            (retainedEnvironment
              ((receivedEnvironment environment intro.parameter description view invocation receipt).extend
                (returnBinder intro.parameter) returned) intro.parameter) := by
  let kernel := closureKernel intro assignment inputs registry declarations readout base ports original
  have localSolves : Satisfies
      (OriginalFormalAdmission.localKernel intro assignment inputs readout (proofAdmissions base) kernel)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body)) := solves
  obtain ⟨description, view, packet, _, _, descriptionAdmitted, viewAdmitted, every⟩ :=
    actual_build_from_whole_telescope intro assignment inputs readout (proofAdmissions base)
      kernel prior annotation localSolves
  refine ⟨description, view, descriptionAdmitted, viewAdmitted, ?_⟩
  intro invocation invocationAdmitted
  obtain ⟨receipt, state, receiptAdmitted, decoded, selected, entry⟩ := every invocation invocationAdmitted
  refine ⟨receipt, receiptAdmitted, ?_⟩
  intro returned returnAdmitted
  have openHistory : (receivedEnvironment (priorEnvironment intro prior) intro.parameter
      description view invocation receipt).replay = none :=
    invocation_receipt_open _ intro.parameter invocation receipt
  obtain ⟨bodyState, bodyDecoded, preserved, body⟩ :=
    value_entry_body_keeps_contract inputs readout intro assignment (proofAdmissions base) kernel
      intro.parameter mode _ openHistory state decoded entry returned returnAdmitted
  exact body_consumer_of_checked_body intro assignment inputs registry declarations readout base ports original
    _ bodyState bodyDecoded (preserved.trans selected) body

/-- The retained Computation entry reaches the same owned body consumer
directly under its receipt/Shared scope, without inventing a Value Return. -/
theorem generated_computation_body_consumer (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (prior : Prior s View) (annotation : Option Declaration)
    (mode : intro.parameter.formal.entry = .computation)
    (solves : Satisfies
      (closureKernel intro assignment inputs registry declarations readout base ports original)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body))) :
    let kernel := closureKernel intro assignment inputs registry declarations readout base ports original
    let environment := priorEnvironment intro prior
    ∃ description view,
      kernel.admitted environment (descriptionBinder intro.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder intro.parameter) description)
        (viewBinder intro.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view)
        (invocationBinder intro.parameter) invocation →
      ∃ receipt,
        kernel.admitted
          (((environment.extend (descriptionBinder intro.parameter) description).extend (viewBinder intro.parameter) view).extend
            (invocationBinder intro.parameter) invocation) (receiptBinder intro.parameter) receipt ∧
        BodyConsumer intro assignment inputs registry declarations readout base ports original
          (retainedEnvironment (receivedEnvironment environment intro.parameter description view invocation receipt)
            intro.parameter) := by
  let kernel := closureKernel intro assignment inputs registry declarations readout base ports original
  have localSolves : Satisfies
      (OriginalFormalAdmission.localKernel intro assignment inputs readout (proofAdmissions base) kernel)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body)) := solves
  obtain ⟨description, view, packet, _, _, descriptionAdmitted, viewAdmitted, every⟩ :=
    actual_build_from_whole_telescope intro assignment inputs readout (proofAdmissions base)
      kernel prior annotation localSolves
  refine ⟨description, view, descriptionAdmitted, viewAdmitted, ?_⟩
  intro invocation invocationAdmitted
  obtain ⟨receipt, state, receiptAdmitted, decoded, selected, entry⟩ := every invocation invocationAdmitted
  obtain ⟨bodyState, bodyDecoded, preserved, body⟩ :=
    computation_entry_body_keeps_contract inputs readout intro assignment (proofAdmissions base) kernel
      intro.parameter mode _ state decoded entry
  exact ⟨receipt, receiptAdmitted,
    body_consumer_of_checked_body intro assignment inputs registry declarations readout base ports original
      _ bodyState bodyDecoded (preserved.trans selected) body⟩

end YulangClosure.OriginalSourceClosure
