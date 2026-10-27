import YulangClosure.OriginalSourceClosure

/-!
Actual generated Value-entry body cut, strengthened with decoder projection
preservation under the SAME EventProof witness. Source Generalize §§3.2–3.3;
see 2026-10-27-original-source-closure.md. This uses the constructed
closureKernel/proofAdmissions instance. It does not establish arbitrary raw
payload conservativity, source membership, Native.World correspondence or
whole Effect hygiene.
-/
namespace YulangClosure.OriginalEventProofCut

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalFormalShared
open OriginalFormalAdmission OriginalCheckingAdmission OriginalSourceChecking
open OriginalSourceClosure

variable {s : Sorts} {View : Type}

/-- Equalities of decoded execution fields; logical eta/witness/views are separate. -/
def ActualFieldsPreserved (before after : Decoded s View) : Prop :=
  after.assignment.descriptor = before.assignment.descriptor ∧
  after.interfaces = before.interfaces ∧
  after.installed = before.installed ∧
  after.assignment.value = before.assignment.value ∧
  after.assignment.root = before.assignment.root ∧
  after.assignment.binding = before.assignment.binding ∧
  after.assignment.event.fiber = before.assignment.event.fiber ∧
  after.assignment.event.eta0 = before.assignment.event.eta0 ∧
  after.assignment.event.history = before.assignment.event.history ∧
  after.assignment.event.current = before.assignment.event.current ∧
  after.assignment.event.scope = before.assignment.event.scope ∧
  after.assignment.event.authority = before.assignment.event.authority ∧
  after.assignment.event.incidence = before.assignment.event.incidence ∧
  after.assignment.event.dictionary = before.assignment.event.dictionary ∧
  after.fixedFrames = before.fixedFrames ∧
  after.callOwners = before.callOwners ∧
  after.active = before.active ∧
  after.activeRaw = before.activeRaw

def BodyConsumerAtCut (intro : Introduction s View) (assignment : FormalAssignment s View)
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
    (∀ raw : RawObservation s,
      Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.body.site, .finalRoot⟩))) →
      Meaning inputs (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.lambdaSite, .bodyConsumer⟩)))) ∧
    ∀ after : Decoded s View,
      decode readout (environment.extend (bodyProofBinder intro.parameter) candidate) = some after →
      ActualFieldsPreserved state after ∧
      after.assignment.event.eta = packet.eta ∧
      after.assignment.event.witness = packet.witness ∧
      after.viewMeaning = packet.viewMeaning


/-- The original consumer's witness proves fields of every actual decoded
successor. No field-preservation premise or selected endpoint equality is supplied. -/
theorem body_consumer_actual_fields (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View))
    (body : BodyConsumer intro assignment inputs registry declarations readout base ports original environment) :
    BodyConsumerAtCut intro assignment inputs registry declarations readout base ports original environment := by
  obtain ⟨state, candidate, packet, decoded, payload, nextDecoded, selected,
    pattern, consumer, source, action⟩ := body
  refine ⟨state, candidate, packet, decoded, payload, nextDecoded, selected,
    pattern, consumer, source, action, ?_⟩
  intro after afterDecoded
  have actualDecoded := decode_extend readout environment
    (bodyProofBinder intro.parameter) candidate state decoded
  simp only [decodeFrame, payload] at actualDecoded
  have same : state.logical packet.encode = after :=
    Option.some.inj (actualDecoded.symm.trans afterDecoded)
  subst after
  exact ⟨proof_packet_preserves state _ packet,
    proof_packet_uses_current_evidence state _ packet⟩

/-- Apply the strengthened cut to the unchanged generated Value Build and
its complete independently admitted invocation/Return quantifiers. -/
theorem generated_value_body_actual_fields (intro : Introduction s View)
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
          BodyConsumerAtCut intro assignment inputs registry declarations readout base ports original
            (retainedEnvironment
              ((receivedEnvironment environment intro.parameter description view invocation receipt).extend
                (returnBinder intro.parameter) returned) intro.parameter) := by
  obtain ⟨description, view, descriptionAdmitted, viewAdmitted, every⟩ :=
    generated_value_body_consumer intro assignment inputs registry declarations readout base ports original
      prior annotation mode solves
  refine ⟨description, view, descriptionAdmitted, viewAdmitted, ?_⟩
  intro invocation invocationAdmitted
  obtain ⟨receipt, receiptAdmitted, returnedBody⟩ := every invocation invocationAdmitted
  refine ⟨receipt, receiptAdmitted, ?_⟩
  intro returned returnAdmitted
  exact body_consumer_actual_fields intro assignment inputs registry declarations readout base ports original
    _ (returnedBody returned returnAdmitted)

end YulangClosure.OriginalEventProofCut
