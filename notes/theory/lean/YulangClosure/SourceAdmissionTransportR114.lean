import YulangClosure.SourceScopedAdmissionR112

/-!
R114: CONSTRUCTED / UNCHECKED. Execution is excluded by the fixed packet.

The positive statements reconstruct actual original constructor subtrees,
retaining all local Checking premises. The negative statement uses a COMPLETE
App Judgment, rather than R112's empty rule shell. It discriminates the current
parametric source-kernel interface; its local predicates are NOT authenticated
instances of the manuscript's original source laws. Thus it is not a
source-semantic counterexample or a refutation of the parent theorem.
-/
namespace YulangClosure.SourceAdmissionTransportR114

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalParameterWorld OriginalFormalShared OriginalSourceClosure

variable {Value : Type}

/-- Reconstruct the exact App continuation, including both finite checks,
all conditional singleton-formal atoms, and both arbitrary original operands.
No environment transport is hidden in this equivalence. -/
theorem app_continuation_iff (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) (callee argument : Source .expression) :
    Judgment kernel environment (LogicalOccurrencesR104.appRule context mark callee argument) ↔
      (∀ premise ∈
        (((([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
          .sourceCallIncidence, .callableImage] : List AtomKind) ++
          (if singletonFormalCall context callee argument then
            [AtomKind.roleAndInitialCallOrigin] else [])).map
          (fun kind => Premise.atom (atom kind mark.site context [callee.site, argument.site]))) ++
          [.checking ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩,
           .checking ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩]),
        Local kernel environment premise) ∧
      SourceJudgment kernel environment context callee ∧
      SourceJudgment kernel environment context argument := by
  constructor
  · intro proof
    cases proof with
    | rule locals children =>
        cases children with
        | cons first rest =>
            cases rest with
            | cons second _ => exact ⟨locals, first, second⟩
  · rintro ⟨locals, first, second⟩
    exact .rule locals (.cons first (.cons second .nil))

/-- Both outer App annotation alternatives expose this SAME checking
obligation at the original ViewLogic telescope, not at the incoming root. -/
theorem app_actual_check (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (source : SourceJudgment kernel environment context (.app mark callee argument)) :
    ∃ candidate, kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
      Checking kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate)
        ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∧
      Judgment kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate)
        (LogicalOccurrencesR104.appRule context mark callee argument) := by
  obtain ⟨candidate, admitted, body⟩ :=
    SourceScopedAdmissionR112.app_witness kernel environment context mark callee argument source
  have locals := ((app_continuation_iff kernel _ context mark callee argument).mp body).1
  have present : Premise.checking
      ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∈
      (((([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
          .sourceCallIncidence, .callableImage] : List AtomKind) ++
          (if singletonFormalCall context callee argument then
            [AtomKind.roleAndInitialCallOrigin] else [])).map
          (fun kind => Premise.atom (atom kind mark.site context [callee.site, argument.site]))) ++
          [.checking ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩,
           .checking ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩]) :=
    List.mem_append_right _ List.mem_cons_self
  cases locals _ present with
  | checking checked => exact ⟨candidate, admitted, checked, body⟩

/-- Reconstruct the ORIGINAL checkedBody, preserving the pattern environment,
the EventProof admission, the body's local consumer atoms and finite Checking.
The same Shared anchor is already in `environment`; no new anchor is chosen. -/
theorem checked_body_iff (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) :
    Judgment kernel environment (checkedBody parameter) ↔
      SourceJudgment kernel environment (formalContext parameter) parameter.pattern ∧
      ∃ candidate, kernel.admitted environment (bodyProofBinder parameter) candidate ∧
        Judgment kernel (environment.extend (bodyProofBinder parameter) candidate)
          (LogicalOccurrencesR104.bodyRule parameter.context ⟨parameter.lambdaSite, none⟩
            parameter.formal parameter.pattern parameter.body) := by
  constructor
  · exact SourceScopedAdmissionR112.body_eventproof kernel environment parameter
  · rintro ⟨pattern, candidate, admitted, body⟩
    apply Judgment.rule (by intro premise impossible; cases impossible)
    exact .cons pattern (.cons (.existsE candidate admitted body) .nil)

/-- The retained continuation reconstructs with the very same designated
anchor. Neither direction selects an independent Shared witness. -/
theorem shared_body_iff (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) :
    Judgment kernel environment (retainedBody parameter) ↔
      kernel.admitted environment (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter)) ∧
      Judgment kernel
        (environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter)))
        (checkedBody parameter) := by
  constructor
  · intro proof
    cases proof with
    | sharedE admitted body => exact ⟨admitted, body⟩
  · rintro ⟨admitted, body⟩
    exact Judgment.sharedE admitted body

/-- Actual Lambda core, with every local closure/entry clause retained.
Desc and ViewLogic are outside ALL independently admitted invocations; receipt
and the unchanged entry continuation remain underneath their own invocation.
Arbitrary formal annotation, entry mode, pattern and body are Parameter fields.
`annotation_child` supplies this core for either outer annotation alternative;
it does not prove transport of the outer annotation's own local evidence. -/
theorem lambda_core_iff (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) :
    Judgment kernel environment (lambdaTree parameter) ↔
      ∃ description, kernel.admitted environment (descriptionBinder parameter) description ∧
      ∃ view, kernel.admitted (environment.extend (descriptionBinder parameter) description)
        (viewBinder parameter) view ∧
      let described := (environment.extend (descriptionBinder parameter) description).extend (viewBinder parameter) view
      (∀ premise ∈ ([AtomKind.captureWholeEnvironment, .closureFormation].map
        (fun kind => Premise.atom (atom kind parameter.lambdaSite parameter.context
          [parameter.formal.site, parameter.pattern.site, parameter.body.site]))),
        Local kernel described premise) ∧
      ∀ invocation, kernel.admitted described (invocationBinder parameter) invocation →
      ∃ receipt, kernel.admitted (described.extend (invocationBinder parameter) invocation)
        (receiptBinder parameter) receipt ∧
      let entered := (described.extend (invocationBinder parameter) invocation).extend (receiptBinder parameter) receipt
      (∀ premise ∈ entryPremises parameter, Local kernel entered premise) ∧
      Judgment kernel entered (enteredBody parameter) := by
  constructor
  · intro proof
    cases proof with
    | existsE description admittedDescription proof =>
        cases proof with
        | existsE view admittedView proof =>
            refine ⟨description, admittedDescription, view, admittedView, ?_⟩
            cases proof with
            | rule locals children =>
                refine ⟨locals, ?_⟩
                cases children with
                | cons universal _ =>
                    cases universal with
                    | forallE every =>
                        intro invocation accepted
                        cases every invocation accepted with
                        | existsE receipt acceptedReceipt proof =>
                            refine ⟨receipt, acceptedReceipt, ?_⟩
                            cases proof with
                            | rule entryLocals entryChildren =>
                                cases entryChildren with
                                | cons body _ => exact ⟨entryLocals, body⟩
  · rintro ⟨description, admittedDescription, view, admittedView, locals, every⟩
    apply Judgment.existsE description admittedDescription
    apply Judgment.existsE view admittedView
    apply Judgment.rule locals
    refine Judgments.cons (Judgment.forallE ?_) Judgments.nil
    intro invocation accepted
    obtain ⟨receipt, acceptedReceipt, entryLocals, body⟩ := every invocation accepted
    exact Judgment.existsE receipt acceptedReceipt (Judgment.rule entryLocals (.cons body .nil))

/-- Both entry modes, INCLUDING fixed replay, keep their original quantifiers.
This equivalence changes no admissions or environments. In a real Lambda
invocation `invocation_receipt_open` selects the open branch; generic fixed
publication replay remains explicitly represented here. -/
theorem entry_telescope_iff (kernel : Kernel Value) (environment : Environment Value)
    (parameter : Parameter) :
    Judgment kernel environment (enteredBody parameter) ↔
      match parameter.formal.entry with
      | .value => match environment.replay with
        | none => ∀ returned, kernel.admitted environment (returnBinder parameter) returned →
            Judgment kernel (environment.extend (returnBinder parameter) returned) (retainedBody parameter)
        | some history => ∃ returned,
            environment.executionValue (returnBinder parameter) = some returned ∧
            kernel.admitted environment (returnBinder parameter) returned ∧
            Judgment kernel (environment.extend (returnBinder parameter) returned) (retainedBody parameter)
      | .computation => Judgment kernel environment (retainedBody parameter) := by
  cases mode : parameter.formal.entry with
  | computation => simp only [enteredBody, mode]
  | value =>
      simp only [enteredBody, mode]
      cases replay : environment.replay with
      | none =>
          constructor
          · intro proof
            cases proof with
            | executionOpen _ every => exact every
            | executionFixed _ impossible _ _ _ _ => simp [replay] at impossible
          · exact Judgment.executionOpen replay
      | some history =>
          constructor
          · intro proof
            cases proof with
            | executionOpen impossible _ => simp [replay] at impossible
            | executionFixed _ _ returned lookup admitted body => exact ⟨returned, lookup, admitted, body⟩
          · rintro ⟨returned, lookup, admitted, body⟩
            exact Judgment.executionFixed history replay returned lookup admitted body

namespace ActualAppDiscriminator

open OriginalCheckingAdmission.Discriminator

def callee : Source .expression := .primitive ⟨3, none⟩ 0
def argument : Source .expression := .literal ⟨4, none⟩ .unit
def source : Source .expression := .app ⟨7, none⟩ callee argument
def root : Root sorts Bool := (baseRoot false).withSource [] source
def initial : Decoded sorts Bool := root.decoded
def start : Environment (Payload sorts Bool) where
  root := .root root
  anchors := fun _ => ⟨.root root, ⟨[], 0⟩⟩
  publications := fun _ => none
  origin := 0
def endpoint : Endpoint := ⟨7, .descriptor⟩
def binder : Binder := ⟨7, .viewLogic, 0⟩
def raw : Logical sorts Bool := ⟨[(endpoint, true)], [], id, (), ()⟩
def candidate : ScopedValue (Payload sorts Bool) := scopeCandidate start 0 (.logical .viewLogic raw)
def ready (environment : Environment (Payload sorts Bool)) : Prop :=
  ∃ state, decode readout environment = some state ∧ state.assignment.descriptor endpoint = true

/-- Explicit LOCAL interface interpretation, not adopted source semantics.
Only the actual descriptorFormation atom tests its App contract. Other atom
clauses and the independently named primitive-check leaves are exposed below. -/
def modelKernel : Kernel (Payload sorts Bool) where
  atom := fun environment atom => atom.kind = .descriptorFormation → ready environment
  admitted := Admitted inputs readout admissions
  primitiveCheck := fun environment _ _ => ready environment
  structuralShape := fun _ _ _ _ => False
  functionShape := fun _ _ _ _ _ => False
  boundaryTag := fun _ _ _ _ _ _ => True
  conversion := fun _ _ _ _ _ _ => True

theorem locals_of_ready (environment : Environment (Payload sorts Bool))
    (available : ready environment) (premise : Premise) : Local modelKernel environment premise := by
  cases premise with
  | atom atom => exact .atom (fun _ => available)
  | checking goal => exact .checking (.primitive goal 0 available)
  | boundary site context lower upper => exact .boundary (.actual site context lower upper 0 True.intro)

theorem raw_ready : ready (start.extend binder candidate) := by
  refine ⟨initial.logical raw, ?_, ?_⟩
  · exact decode_extend readout start binder candidate initial rfl
  · simp [Decoded.logical, raw, put]

/-- Complete actual source App: both source children, both original finite
checks and all five ordinary App atoms are present, not an empty rule shell. -/
theorem original_source_judgment : SourceJudgment modelKernel start [] source := by
  have admitted : modelKernel.admitted start binder candidate :=
    (admitted_scoped_iff inputs readout admissions start binder initial rfl 0 _).mpr
      ⟨rfl, True.intro⟩
  change Judgment modelKernel start (.existsE binder (LogicalOccurrencesR104.appRule [] ⟨7, none⟩ callee argument))
  apply Judgment.existsE candidate admitted
  apply Judgment.rule (fun premise _ => locals_of_ready _ raw_ready premise)
  apply Judgments.cons
  · exact Judgment.rule (fun premise _ => locals_of_ready _ raw_ready premise) Judgments.nil
  · exact Judgments.cons
      (Judgment.rule (fun premise _ => locals_of_ready _ raw_ready premise) Judgments.nil) Judgments.nil

/-- Every empty-descriptor replacement fails the actual App formation atom,
even if its view/eta/witness fields are independently reselected. Admission
and the original actual event incidence are not used as a shortcut here. -/
theorem no_normalized_continuation (data : Logical sorts Bool)
    (empty : data.descriptors = []) (occurrence : Nat) :
    ¬ Judgment modelKernel
      (start.extend binder (scopeCandidate start occurrence (.logical .viewLogic data)))
      (LogicalOccurrencesR104.appRule [] ⟨7, none⟩ callee argument) := by
  intro proof
  cases proof with
  | rule locals _ =>
      have present : Premise.atom (atom .descriptorFormation 7 [] [callee.site, argument.site]) ∈
          (((([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
              .sourceCallIncidence, .callableImage] : List AtomKind) ++
              (if singletonFormalCall [] callee argument then [AtomKind.roleAndInitialCallOrigin] else [])).map
              (fun kind => Premise.atom (atom kind 7 [] [callee.site, argument.site]))) ++
            [.checking ⟨.value, 7, [], ⟨callee.site, .returnedValue⟩, ⟨7, .descriptor⟩⟩,
             .checking ⟨.computation, 7, [], ⟨7, .callableImage⟩, ⟨7, .synthesis⟩⟩]) := by
        simp [singletonFormalCall, callee]
      cases locals _ present with
      | atom valid =>
          obtain ⟨state, decoded, contract⟩ := valid rfl
          have expected := decode_extend readout start binder
            (scopeCandidate start occurrence (.logical .viewLogic data)) initial rfl
          have same : state = initial.logical data := Option.some.inj (decoded.symm.trans expected)
          subst state
          simpa [Decoded.logical, empty, put, initial, root, Root.withSource,
            Root.decoded, baseRoot, endpoint] using contract

end ActualAppDiscriminator

-- Future verification owner: these commands have NOT RUN in R114.
#check @YulangClosure.SourceAdmissionTransportR114.app_continuation_iff
#print axioms YulangClosure.SourceAdmissionTransportR114.app_continuation_iff
#check @YulangClosure.SourceAdmissionTransportR114.app_actual_check
#print axioms YulangClosure.SourceAdmissionTransportR114.app_actual_check
#check @YulangClosure.SourceAdmissionTransportR114.checked_body_iff
#print axioms YulangClosure.SourceAdmissionTransportR114.checked_body_iff
#check @YulangClosure.SourceAdmissionTransportR114.shared_body_iff
#print axioms YulangClosure.SourceAdmissionTransportR114.shared_body_iff
#check @YulangClosure.SourceAdmissionTransportR114.lambda_core_iff
#print axioms YulangClosure.SourceAdmissionTransportR114.lambda_core_iff
#check @YulangClosure.SourceAdmissionTransportR114.entry_telescope_iff
#print axioms YulangClosure.SourceAdmissionTransportR114.entry_telescope_iff
#check @YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.locals_of_ready
#print axioms YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.locals_of_ready
#check @YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.raw_ready
#print axioms YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.raw_ready
#check @YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.original_source_judgment
#print axioms YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.original_source_judgment
#check @YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.no_normalized_continuation
#print axioms YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.no_normalized_continuation

end YulangClosure.SourceAdmissionTransportR114
