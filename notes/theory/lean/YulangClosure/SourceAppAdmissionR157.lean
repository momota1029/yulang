import YulangClosure.SourceAdmissionTransportR114

/-!
R157 CONSTRUCTED / UNCHECKED. The fixed packet excludes Lean execution.

SG §§3.1--3.3 and 5.2 retain the description selected by the actual App.
The original App has a ViewLogic binder, with no preceding Desc binder.
This module recovers its exact admitted payload and original continuation;
it does not impose the empty-write Lambda ViewPacket grammar on that payload.

The final lemmas expose the decoder obstruction to clearing description
writes. Decoder equality alone is not admission or Judgment transport:
Kernel predicates can observe the full Environment, including its frames.
No concrete source law or parent soundness theorem is supplied here.
-/
namespace YulangClosure.SourceAppAdmissionR157

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment

variable {s : Sorts} {View : Type}

/-- Exact original App premises, including both conditional-origin branches
and the two finite Checking judgments. No local clause is replaced by True. -/
def appPremises (context : Context) (mark : Mark)
    (callee argument : Source .expression) : List Premise :=
  ((([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
      .sourceCallIncidence, .callableImage] : List AtomKind) ++
      (if singletonFormalCall context callee argument then
        [AtomKind.roleAndInitialCallOrigin] else [])).map
      (fun kind => Premise.atom (atom kind mark.site context [callee.site, argument.site]))) ++
    [.checking ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩,
     .checking ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩]

/-- Admission at the ORIGINAL App binder classifies the payload and recovers
its exact scope and occurrence. Descriptor/interface lists remain arbitrary.
The original LocalAdmissions record is used without a record update. -/
theorem admitted_view_payload (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (site : Site) (candidate : ScopedValue (Payload s View))
    (accepted : Admitted inputs readout admissions environment ⟨site, .viewLogic, 0⟩ candidate) :
    ∃ occurrence data state,
      candidate = scopeCandidate environment occurrence (.logical .viewLogic data) ∧
      decode readout environment = some state ∧
      admissions.logical state ⟨site, .viewLogic, 0⟩ .viewLogic data := by
  obtain ⟨parents, state, decoded, valid⟩ := accepted
  rcases candidate with ⟨payload, ⟨path, occurrence⟩⟩
  change path = environment.eventPath at parents
  subst path
  cases payload with
  | root data => exact False.elim valid
  | shared data => simp [DataAdmitted] at valid
  | runtime data => cases data <;> simp [DataAdmitted] at valid
  | logical kind data =>
      cases kind <;>
        simp only [DataAdmitted, LogicalKind.binderKind, reduceCtorEq, false_and] at valid
      exact ⟨occurrence, data, state, rfl, decoded, valid.2⟩

/-- Invert the actual App continuation into every Local and both arbitrary
source children. This reuses R114 at the unchanged environment and kernel. -/
theorem app_continuation_exact (kernel : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression)
    (derivation : Judgment kernel environment
      (LogicalOccurrencesR104.appRule context mark callee argument)) :
    (∀ premise ∈ appPremises context mark callee argument, Local kernel environment premise) ∧
      SourceJudgment kernel environment context callee ∧
      SourceJudgment kernel environment context argument := by
  exact (SourceAdmissionTransportR114.app_continuation_iff
    kernel environment context mark callee argument).mp derivation

/-- The first formation atom and BOTH original finite checks are conclusions
of the original continuation. This introduces no preservation hypothesis. -/
theorem app_formation_and_checks (kernel : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression)
    (derivation : Judgment kernel environment
      (LogicalOccurrencesR104.appRule context mark callee argument)) :
    kernel.atom environment (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
      Checking kernel environment
        ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∧
      Checking kernel environment
        ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ := by
  have locals := (app_continuation_exact kernel environment context mark callee argument derivation).1
  have formation : Local kernel environment
      (.atom (atom .descriptorFormation mark.site context [callee.site, argument.site])) :=
    locals _ (by simp [appPremises])
  have valueCheck : Local kernel environment (.checking
      ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩) :=
    locals _ (List.mem_append_right _ List.mem_cons_self)
  have computationCheck : Local kernel environment (.checking
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩) :=
    locals _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  cases formation with
  | atom formed =>
      cases valueCheck with
      | checking checkedValue =>
          cases computationCheck with
          | checking checkedComputation => exact ⟨formed, checkedValue, checkedComputation⟩

/-- Construct the exact admitted original App witness from an original
source derivation, for BOTH outer annotation alternatives. This is a lossless
reconstruction, not empty-write normalization. All locals, both finite checks,
both source operands and the entire continuation use this SAME extension.
The descriptor/interface choices are the actual raw packet's writes. -/
theorem app_admission_exact (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression)
    (source : SourceJudgment (admissionKernel inputs readout admissions original)
      environment context (.app mark callee argument)) :
    ∃ occurrence data state,
      decode readout environment = some state ∧
      admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
      let kernel := admissionKernel inputs readout admissions original
      let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
      let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
      kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
      decode readout after = some (state.logical data) ∧
      (state.logical data).assignment.descriptor = put state.assignment.descriptor data.descriptors ∧
      (state.logical data).interfaces = put state.interfaces data.interfaces ∧
      (∀ premise ∈ appPremises context mark callee argument, Local kernel after premise) ∧
      kernel.atom after (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
      Checking kernel after
        ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∧
      Checking kernel after
        ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ ∧
      SourceJudgment kernel after context callee ∧
      SourceJudgment kernel after context argument ∧
      Judgment kernel after (LogicalOccurrencesR104.appRule context mark callee argument) := by
  let kernel := admissionKernel inputs readout admissions original
  obtain ⟨candidate, accepted, continuation⟩ :=
    SourceScopedAdmissionR112.app_witness kernel environment context mark callee argument source
  obtain ⟨occurrence, data, state, same, decoded, localAdmission⟩ :=
    admitted_view_payload inputs readout admissions environment mark.site candidate accepted
  subst candidate
  obtain ⟨locals, calleeProof, argumentProof⟩ :=
    app_continuation_exact kernel _ context mark callee argument continuation
  obtain ⟨formation, valueCheck, computationCheck⟩ :=
    app_formation_and_checks kernel _ context mark callee argument continuation
  refine ⟨occurrence, data, state, decoded, localAdmission, accepted, ?_, rfl, rfl,
    locals, formation, valueCheck, computationCheck, calleeProof, argumentProof, continuation⟩
  exact decode_extend readout environment ⟨mark.site, .viewLogic, 0⟩ _ state decoded

/-- Clearing writes retains the independent logical proof fields, but is
only a candidate operation on payload data. No source admission is implied. -/
def clearWrites (data : Logical s View) : Logical s View :=
  {data with descriptors := [], interfaces := []}

/-- Exact decoder condition for clearing descriptor/interface writes while
retaining their choices. No condition is inferred from a source judgment.
Even this equality does not transport arbitrary Kernel predicates on frames. -/
theorem clear_writes_contract_iff (state : Decoded s View) (data : Logical s View) :
    ((state.logical (clearWrites data)).assignment.descriptor = (state.logical data).assignment.descriptor ∧
      (state.logical (clearWrites data)).interfaces = (state.logical data).interfaces) ↔
    (put state.assignment.descriptor data.descriptors = state.assignment.descriptor ∧
      put state.interfaces data.interfaces = state.interfaces) := by
  change (state.assignment.descriptor = put state.assignment.descriptor data.descriptors ∧
      state.interfaces = put state.interfaces data.interfaces) ↔ _
  exact ⟨fun equal => ⟨equal.1.symm, equal.2.symm⟩,
    fun equal => ⟨equal.1.symm, equal.2.symm⟩⟩

/-- Any empty-descriptor replacement, with arbitrarily reselected proof
fields, loses an actually introduced descriptor. No kernel is changed. -/
theorem changed_descriptor_excludes_empty_replacement
    (state : Decoded s View) (data replacement : Logical s View) (point : Endpoint)
    (empty : replacement.descriptors = [])
    (changed : put state.assignment.descriptor data.descriptors point ≠ state.assignment.descriptor point) :
    (state.logical replacement).assignment.descriptor point ≠
      (state.logical data).assignment.descriptor point := by
  intro equal
  apply changed
  simpa only [Decoded.logical, empty, put_nil] using equal.symm

/-- The same obstruction applies independently to the actual interface. -/
theorem changed_interface_excludes_empty_replacement
    (state : Decoded s View) (data replacement : Logical s View) (point : Endpoint)
    (empty : replacement.interfaces = [])
    (changed : put state.interfaces data.interfaces point ≠ state.interfaces point) :
    (state.logical replacement).interfaces point ≠ (state.logical data).interfaces point := by
  intro equal
  apply changed
  simpa only [Decoded.logical, empty, put_nil] using equal.symm

-- NOT RUN. Future verification owner must inspect every complete type and
-- transitive axiom list, then obtain independent source/proof review.
#check @YulangClosure.SourceAppAdmissionR157.admitted_view_payload
#print axioms YulangClosure.SourceAppAdmissionR157.admitted_view_payload
#check @YulangClosure.SourceAppAdmissionR157.app_continuation_exact
#print axioms YulangClosure.SourceAppAdmissionR157.app_continuation_exact
#check @YulangClosure.SourceAppAdmissionR157.app_formation_and_checks
#print axioms YulangClosure.SourceAppAdmissionR157.app_formation_and_checks
#check @YulangClosure.SourceAppAdmissionR157.app_admission_exact
#print axioms YulangClosure.SourceAppAdmissionR157.app_admission_exact
#check @YulangClosure.SourceAppAdmissionR157.clear_writes_contract_iff
#print axioms YulangClosure.SourceAppAdmissionR157.clear_writes_contract_iff
#check @YulangClosure.SourceAppAdmissionR157.changed_descriptor_excludes_empty_replacement
#print axioms YulangClosure.SourceAppAdmissionR157.changed_descriptor_excludes_empty_replacement
#check @YulangClosure.SourceAppAdmissionR157.changed_interface_excludes_empty_replacement
#print axioms YulangClosure.SourceAppAdmissionR157.changed_interface_excludes_empty_replacement

end YulangClosure.SourceAppAdmissionR157
