import YulangClosure.OriginalSourceClosure
import YulangClosure.SourceLogicalOwnerBridgeR105

/-!
R112 CONSTRUCTED / UNCHECKED. The sprint forbids Lean/Lake/checker execution.
No printed type or axiom result has been obtained for any declaration below.

SG §§3.3/5.2: original judgments contain scoped choices, but the abstract
logical admission interface does not authenticate their source payload laws.
These inversion lemmas preserve the original kernel, operands, witnesses and
environments. The discriminator concerns that interface, not a source-qualified
counterexample to the original intrusion theorem.
-/
namespace YulangClosure.SourceScopedAdmissionR112

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalParameterWorld OriginalFormalShared OriginalSourceClosure

variable {Value : Type}

/-- Both optional outer annotation alternatives retain the original App body.
The annotation's own local proofs remain in the input derivation. -/
theorem app_witness (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (source : SourceJudgment kernel environment context (.app mark callee argument)) :
    ∃ candidate, kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
      Judgment kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate)
        (LogicalOccurrencesR104.appRule context mark callee argument) := by
  rcases mark with ⟨site, annotation⟩
  cases annotation with
  | none =>
      simp only [SourceJudgment, sourceRules] at source
      cases source with
      | existsE candidate accepted body => exact ⟨candidate, accepted, body⟩
  | some target =>
      simp only [SourceJudgment, sourceRules] at source
      cases source with
      | rule _ children =>
          cases children with
          | cons first _ =>
              cases first with
              | existsE candidate accepted body => exact ⟨candidate, accepted, body⟩

/-- The same Desc and ViewLogic witnesses precede every admitted invocation.
Receipt and the entry continuation stay beneath that invocation. No fresh
per-challenge Desc/ViewLogic is selected. -/
theorem lambda_telescope (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (annotation : Option Declaration)
    (source : SourceJudgment kernel environment parameter.context
      (.lambda ⟨parameter.lambdaSite, annotation⟩ parameter.formal parameter.pattern parameter.body)) :
    ∃ description, kernel.admitted environment (descriptionBinder parameter) description ∧
    ∃ view, kernel.admitted (environment.extend (descriptionBinder parameter) description)
      (viewBinder parameter) view ∧
    ∀ invocation, kernel.admitted
      ((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view)
      (invocationBinder parameter) invocation →
    ∃ receipt, kernel.admitted
      (((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend
        (invocationBinder parameter) invocation) (receiptBinder parameter) receipt ∧
      Judgment kernel
        ((((environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view).extend
          (invocationBinder parameter) invocation).extend (receiptBinder parameter) receipt)
        (enteredBody parameter) := by
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

/-- The pattern uses the unchanged environment. EventProof and the whole
original body consumer use its exact extension, retaining every local premise. -/
theorem body_eventproof (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (proof : Judgment kernel environment (checkedBody parameter)) :
    SourceJudgment kernel environment (OriginalFormalShared.formalContext parameter) parameter.pattern ∧
    ∃ candidate, kernel.admitted environment (bodyProofBinder parameter) candidate ∧
      Judgment kernel (environment.extend (bodyProofBinder parameter) candidate)
        (LogicalOccurrencesR104.bodyRule parameter.context ⟨parameter.lambdaSite, none⟩
          parameter.formal parameter.pattern parameter.body) := by
  cases proof with
  | rule _ children =>
      cases children with
      | cons pattern rest =>
          cases rest with
          | cons proof _ =>
              cases proof with
              | existsE candidate accepted body => exact ⟨pattern, candidate, accepted, body⟩

/-- Value mode keeps every admitted Return/rebind beneath the invocation.
`invocation_receipt_open` supplies openHistory at the actual receipt environment.
The Shared witness is the original anchor, never an independent replacement. -/
theorem value_body_telescope (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (mode : parameter.formal.entry = .value)
    (openHistory : environment.replay = none)
    (entry : Judgment kernel environment (enteredBody parameter)) :
    ∀ returned, kernel.admitted environment (returnBinder parameter) returned →
      let after := environment.extend (returnBinder parameter) returned
      kernel.admitted after (sharedBinder parameter) (after.anchorValue (sharedBinder parameter)) ∧
      (SourceJudgment kernel
        (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter)))
        (OriginalFormalShared.formalContext parameter) parameter.pattern ∧
      ∃ candidate, kernel.admitted
        (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter)))
        (bodyProofBinder parameter) candidate ∧
        Judgment kernel
          ((after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))).extend
            (bodyProofBinder parameter) candidate)
          (LogicalOccurrencesR104.bodyRule parameter.context ⟨parameter.lambdaSite, none⟩
            parameter.formal parameter.pattern parameter.body)) := by
  intro returned accepted
  obtain ⟨shared, body⟩ := value_entry_shared kernel environment parameter mode openHistory entry returned accepted
  exact ⟨shared, body_eventproof kernel _ parameter body⟩

/-- Computation mode keeps its original carrier/receipt entry and Shared
anchor. It introduces no Value Return/rebind. -/
theorem computation_body_telescope (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) (mode : parameter.formal.entry = .computation)
    (entry : Judgment kernel environment (enteredBody parameter)) :
    kernel.admitted environment (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter)) ∧
    (SourceJudgment kernel
      (environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter)))
      (OriginalFormalShared.formalContext parameter) parameter.pattern ∧
    ∃ candidate, kernel.admitted
      (environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter)))
      (bodyProofBinder parameter) candidate ∧
      Judgment kernel
        ((environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter))).extend
          (bodyProofBinder parameter) candidate)
        (LogicalOccurrencesR104.bodyRule parameter.context ⟨parameter.lambdaSite, none⟩
          parameter.formal parameter.pattern parameter.body)) := by
  obtain ⟨shared, body⟩ := computation_entry_shared kernel environment parameter mode entry
  exact ⟨shared, body_eventproof kernel _ parameter body⟩

namespace InterfaceCountermodel

-- Reuse the pinned, explicit Bool/Unit model of the original interface.
open OriginalCheckingAdmission.Discriminator

def endpoint : Endpoint := ⟨7, .descriptor⟩

def packet : Logical sorts Bool :=
  ⟨[(endpoint, true)], [(endpoint, true)], id, (), ()⟩

/-- Both original logical classes admit a packet which changes the descriptor
and interface. This model uses the unmodified DataAdmitted definition. -/
theorem admits_writes :
    DataAdmitted inputs readout admissions (state false) ⟨7, .viewLogic, 0⟩ (.logical .viewLogic packet) ∧
    DataAdmitted inputs readout admissions (state false) ⟨7, .eventProof, 0⟩ (.logical .eventProof packet) :=
  ⟨⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩⟩

theorem scoped_admits_writes :
    Admitted inputs readout admissions (environment false) ⟨7, .viewLogic, 0⟩
      (scopeCandidate (environment false) 0 (.logical .viewLogic packet)) ∧
    Admitted inputs readout admissions (environment false) ⟨7, .eventProof, 0⟩
      (scopeCandidate (environment false) 0 (.logical .eventProof packet)) := by
  constructor
  · exact (admitted_scoped_iff inputs readout admissions (environment false) _ (state false) rfl 0 _).mpr
      admits_writes.1
  · exact (admitted_scoped_iff inputs readout admissions (environment false) _ (state false) rfl 0 _).mpr
      admits_writes.2

/-- The admitted packet can occur in an actual original Judgment derivation.
This deliberately small rule shell is an interface model, not a derivation
of a complete source App/Lambda or a counterexample to source soundness. -/
theorem shell_judgment (original : Kernel (Payload sorts Bool)) (kind : LogicalKind) :
    Judgment (admissionKernel inputs readout admissions original) (environment false)
      (.existsE ⟨7, kind.binderKind, 0⟩ (.rule .sequence 7 [] [] .nil)) := by
  let candidate := scopeCandidate (environment false) 0 (.logical kind packet)
  have accepted : Admitted inputs readout admissions (environment false)
      ⟨7, kind.binderKind, 0⟩ candidate :=
    (admitted_scoped_iff inputs readout admissions (environment false) _ (state false) rfl 0 _).mpr
      ⟨rfl, True.intro⟩
  apply Judgment.existsE candidate accepted
  exact Judgment.rule (by intro premise member; cases member) Judgments.nil

theorem changes_contract_fields :
    (state false).assignment.descriptor endpoint = false ∧
    ((state false).logical packet).assignment.descriptor endpoint = true ∧
    (state false).interfaces endpoint = false ∧
    ((state false).logical packet).interfaces endpoint = true := by
  exact ⟨rfl, by simp [Decoded.logical, packet, put], rfl,
    by simp [Decoded.logical, packet, put]⟩

/-- The extra EventProof wrapper excludes this original-interface candidate;
therefore its use requires a source-owned normalization/transport law. -/
theorem proof_wrapper_rejects :
    ¬ (proofAdmissions admissions).logical (state false) ⟨7, .eventProof, 0⟩ .eventProof packet := by
  simp [proofAdmissions, OriginalCheckingAdmission.Discriminator.admissions, packet]

theorem no_event_packet_encoding (owner : OriginalSourceEvents.Owner)
    (candidate : EventProofPacket sorts Bool owner) : packet ≠ candidate.encode := by
  intro equal
  have descriptors := congrArg Logical.descriptors equal
  simp [packet, EventProofPacket.encode] at descriptors

end InterfaceCountermodel

-- Audit commands are intentionally present but NOT EXECUTED in R112.
#check @YulangClosure.SourceScopedAdmissionR112.app_witness
#print axioms YulangClosure.SourceScopedAdmissionR112.app_witness
#check @YulangClosure.SourceScopedAdmissionR112.lambda_telescope
#print axioms YulangClosure.SourceScopedAdmissionR112.lambda_telescope
#check @YulangClosure.SourceScopedAdmissionR112.body_eventproof
#print axioms YulangClosure.SourceScopedAdmissionR112.body_eventproof
#check @YulangClosure.SourceScopedAdmissionR112.value_body_telescope
#print axioms YulangClosure.SourceScopedAdmissionR112.value_body_telescope
#check @YulangClosure.SourceScopedAdmissionR112.computation_body_telescope
#print axioms YulangClosure.SourceScopedAdmissionR112.computation_body_telescope
#check @YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.admits_writes
#print axioms YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.admits_writes
#check @YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.scoped_admits_writes
#print axioms YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.scoped_admits_writes
#check @YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.shell_judgment
#print axioms YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.shell_judgment
#check @YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.changes_contract_fields
#print axioms YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.changes_contract_fields
#check @YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.proof_wrapper_rejects
#print axioms YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.proof_wrapper_rejects
#check @YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.no_event_packet_encoding
#print axioms YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.no_event_packet_encoding

end YulangClosure.SourceScopedAdmissionR112
