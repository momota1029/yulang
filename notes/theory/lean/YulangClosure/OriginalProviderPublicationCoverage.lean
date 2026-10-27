import YulangClosure.OriginalProviderSourceSolution

/-! Publication coverage for the unchanged source rules. None of the semantic
inputs below is inferred for the Rust provider. In particular nonempty Return
admission, open replay, compatibility and the local source proofs have owners. -/
namespace YulangClosure.OriginalProviderPublicationCoverage

open OriginalSource OriginalProviderSourceSolution
open OriginalSourceInterpretation OriginalSourceEnvironment

def FiniteSupport {Value : Type}
    (map : PublicationId Value → Option (PublicationRecord Value)) : Prop :=
  ∃ keys : List (PublicationId Value), ∀ key record, map key = some record → key ∈ keys

def keyBound {Value : Type} (key : PublicationId Value) : Nat :=
  (key.path.map EventStep.occurrence).sum

def supportBound {Value : Type} : List (PublicationId Value) → Nat
  | [] => 0
  | key :: rest => keyBound key + 1 + supportBound rest

theorem key_bound_lt_support {Value : Type} (keys : List (PublicationId Value))
    (key : PublicationId Value) (member : key ∈ keys) :
    keyBound key < supportBound keys := by
  induction keys with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [supportBound]
    rcases member with equal | member
    · subst key; omega
    · have bound := ih member; omega

/-- Original admission ignores the occurrence but retains the same data and
complete original parent path. This derives re-scoping; it is not an added law. -/
theorem rescope_admitted {s : Sorts} {View : Type} (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (returned : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions environment binder returned)
    (occurrence : Nat) :
    Admitted inputs readout admissions environment binder
      (scopeCandidate environment occurrence returned.data) := by
  exact ⟨rfl, admitted.2⟩

/-- Any finite-support map fails the actual universal open source judgment,
provided one genuine Return payload is admitted. Empty prior maps are unnecessary
for this stronger obstruction; no conclusion concerns an authenticated provider. -/
theorem finite_support_no_open_provider {s : Sorts} {View : Type}
    (o : Occurrences) (context : Context) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (finite : FiniteSupport environment.publications)
    (openHistory : environment.replay = none)
    (returned : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned) :
    ¬ SourceJudgment (admissionKernel inputs readout admissions original)
      environment context o.source := by
  intro solution
  obtain ⟨keys, covers⟩ := finite
  let fresh := scopeCandidate (environment.enterInitializer o.binding)
    (supportBound keys) returned.data
  have freshAdmitted := rescope_admitted inputs readout admissions
    (environment.enterInitializer o.binding) o.returnBinder returned admitted (supportBound keys)
  have found := provider_solution_requires_fixed_record o context
    (admissionKernel inputs readout admissions original) environment solution openHistory fresh freshAdmitted
  have bound := key_bound_lt_support keys (publicationIdentity o environment fresh)
    (covers _ _ found)
  have large : supportBound keys ≤ keyBound (publicationIdentity o environment fresh) := by
    simp [keyBound, publicationIdentity, returnFrame, Frame.exitPath, ActualEvent.path,
      fresh, scopeCandidate, Environment.enterInitializer, List.sum_append]
  omega

theorem finite_completion_support {Value : Type} (o : Occurrences)
    (environment : Environment Value) (events : List (ScopedValue Value))
    (emptyPrior : ∀ key, environment.publications key = none) :
    FiniteSupport (finiteCompletion o environment events) := by
  classical
  refine ⟨events.map (publicationIdentity o environment), ?_⟩
  intro key record found
  simp only [finiteCompletion, emptyPrior key] at found
  cases selected : events.find? (fun returned => decide (publicationIdentity o environment returned = key)) with
  | none => simp [selected] at found
  | some returned =>
    have equal : publicationIdentity o environment returned = key :=
      of_decide_eq_true (List.find?_some (p := fun value => decide (publicationIdentity o environment value = key)) selected)
    exact List.mem_map.mpr ⟨returned, List.mem_of_find?_eq_some selected, equal⟩

theorem empty_prior_finite_completion_no_provider {s : Sorts} {View : Type}
    (o : Occurrences) (context : Context) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (events : List (ScopedValue (Payload s View)))
    (emptyPrior : ∀ key, environment.publications key = none)
    (openHistory : environment.replay = none)
    (returned : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned) :
    ¬ SourceJudgment (admissionKernel inputs readout admissions original)
      {environment with publications := finiteCompletion o environment events} context o.source := by
  exact finite_support_no_open_provider o context inputs readout admissions original _
    (finite_completion_support o environment events emptyPrior) openHistory returned admitted

/-- A publication graph indexed by every original admitted Return, with prior
records winning. It is a total function with optional values, not a finite list. -/
noncomputable def totalCompletion {s : Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (Payload s View))
    (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) :
    PublicationId (Payload s View) → Option (PublicationRecord (Payload s View)) := by
  classical
  exact fun key => match environment.publications key with
    | some record => some record
    | none => if witness : ∃ returned,
        Admitted inputs readout admissions (environment.enterInitializer o.binding) o.returnBinder returned ∧
        publicationIdentity o environment returned = key
      then some (publicationRecord o environment (Classical.choose witness)) else none

def Compatible {s : Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (Payload s View))
    (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) : Prop :=
  ∀ returned, Admitted inputs readout admissions
    (environment.enterInitializer o.binding) o.returnBinder returned →
    ∀ prior, environment.publications (publicationIdentity o environment returned) = some prior →
      prior = publicationRecord o environment returned

theorem total_completion_preserves_prior {s : Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (Payload s View))
    (inputs : Inputs s) (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (key : PublicationId (Payload s View)) (record : PublicationRecord (Payload s View))
    (prior : environment.publications key = some record) :
    totalCompletion o environment inputs readout admissions key = some record := by
  simp only [totalCompletion, prior]

theorem total_completion_contains_admitted {s : Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (Payload s View))
    (inputs : Inputs s) (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (compatible : Compatible o environment inputs readout admissions)
    (returned : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned) :
    totalCompletion o environment inputs readout admissions (publicationIdentity o environment returned) =
      some (publicationRecord o environment returned) := by
  classical
  unfold totalCompletion
  split
  next prior found => exact congrArg some (compatible returned admitted prior found)
  next missing =>
    have witness : ∃ other, Admitted inputs readout admissions
        (environment.enterInitializer o.binding) o.returnBinder other ∧
        publicationIdentity o environment other = publicationIdentity o environment returned :=
      ⟨returned, admitted, rfl⟩
    rw [dite_eq_left witness]
    exact congrArg some (scoped_candidates_agree o environment _ returned
      (Classical.choose_spec witness).1.1 admitted.1 (Classical.choose_spec witness).2)

/-- Exact compatibility is necessary and sufficient for preserving all prior
records while covering every admitted complete candidate record. -/
theorem compatible_iff_extension_exists {s : Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (Payload s View))
    (inputs : Inputs s) (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View) :
    Compatible o environment inputs readout admissions ↔
    ∃ map : PublicationId (Payload s View) → Option (PublicationRecord (Payload s View)),
      (∀ key record, environment.publications key = some record → map key = some record) ∧
      (∀ returned, Admitted inputs readout admissions
        (environment.enterInitializer o.binding) o.returnBinder returned →
        map (publicationIdentity o environment returned) = some (publicationRecord o environment returned)) := by
  constructor
  · intro compatible
    exact ⟨totalCompletion o environment inputs readout admissions,
      total_completion_preserves_prior o environment inputs readout admissions,
      total_completion_contains_admitted o environment inputs readout admissions compatible⟩
  · rintro ⟨map, prior, covers⟩ returned admitted record found
    exact Option.some.inj ((prior _ _ found).symm.trans (covers returned admitted))

theorem total_completion_publication_valid {s : Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (Payload s View))
    (inputs : Inputs s) (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (compatible : Compatible o environment inputs readout admissions)
    (returned : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned) :
    (completedCut o {environment with publications := totalCompletion o environment inputs readout admissions} returned).publicationValid
      [(o.providerName, o.binding)] := by
  intro binding member
  have equal : binding = (o.providerName, o.binding) := by simpa using member
  subst binding
  exact ⟨publicationIdentity o environment returned, publicationRecord o environment returned,
    completed_cut_candidate o _ returned,
    total_completion_contains_admitted o environment inputs readout admissions compatible returned admitted⟩

/-- Explicit original local premises of the identity Lambda. This is a
conditional proof interface, not a concrete instance or a new typing relation. -/
def lambdaAtoms (o : Occurrences) (context : Context) : List Premise :=
  [.atom (atom .captureWholeEnvironment o.closure context [o.formal, o.pattern, o.body]),
   .atom (atom .closureFormation o.closure context [o.formal, o.pattern, o.body])]

def entryAtoms (o : Occurrences) (context : Context) : List Premise :=
  [.atom {(atom .sourceFormalRole o.formal (o.bodyContext context)) with entry := some .value},
   .atom (atom .receiptFormation o.formal (o.bodyContext context) [o.closure, o.pattern, o.body]),
   .atom (atom .entryForceReturnRebind o.formal (o.bodyContext context) [o.closure, o.pattern, o.body])]

def bodyAtoms (o : Occurrences) (context : Context) : List Premise :=
  [.atom (atom .completeBodyConsumer o.body (o.bodyContext context) [o.closure, o.formal]),
   .atom (atom .actualReturnOrPendingSuffix o.body (o.bodyContext context) [o.closure, o.formal]),
   .checking ⟨.computation, o.body, o.bodyContext context,
     ⟨o.body, .finalRoot⟩, ⟨o.closure, .bodyConsumer⟩⟩]

def nameAtoms (o : Occurrences) (context : Context) : List Premise :=
  [.atom {(atom .resolvedSameBinding o.body (o.bodyContext context)) with
     names := [o.formalName], binding := lookupBinding (o.bodyContext context) o.formalName},
   .atom {(atom .computedFetchOnce o.body (o.bodyContext context)) with
     names := [o.formalName], binding := lookupBinding (o.bodyContext context) o.formalName}]

def initializerTree (o : Occurrences) (context : Context) : RuleTree :=
  let name := .rule .name o.body (o.bodyContext context) (nameAtoms o context) .nil
  let body := .existsE ⟨o.body, .eventProof, 0⟩
    (.rule .sequence o.body (o.bodyContext context) (bodyAtoms o context) (.one name))
  let wild := .rule .wild o.pattern (o.bodyContext context) [] .nil
  let checked := .rule .sequence o.formal (o.bodyContext context) [] (.two wild body)
  let entered := .executionE ⟨o.formal, .returnRebind, 0⟩
    (.sharedE ⟨o.formal, .shared, 0⟩ checked)
  let parameter := .existsE ⟨o.formal, .receipt, 0⟩
    (.rule .parameterEntry o.formal (o.bodyContext context) (entryAtoms o context) (.one entered))
  .existsE ⟨o.formal, .description, 0⟩
    (.existsE ⟨o.closure, .viewLogic, 0⟩
      (.rule .lambda o.closure context (lambdaAtoms o context)
        (.one (.forallE ⟨o.closure, .invocation, 0⟩ parameter))))

theorem initializer_source_rules (o : Occurrences) (context : Context) :
    sourceRules context o.initializer = initializerTree o context := by
  simp! [Occurrences.initializer, sourceRules, Source.nameCount, initializerTree,
    lambdaAtoms, entryAtoms, bodyAtoms, nameAtoms, Occurrences.bodyContext, lookupBinding]
  first
  | rfl
  | cbv <;> simp

def InitializerPremises {Value : Type} (o : Occurrences) (context : Context)
    (kernel : Kernel Value) (environment : Environment Value) : Prop :=
  ∃ description, kernel.admitted environment ⟨o.formal, .description, 0⟩ description ∧
  ∃ view, kernel.admitted (environment.extend ⟨o.formal, .description, 0⟩ description)
    ⟨o.closure, .viewLogic, 0⟩ view ∧
  let closure := (environment.extend ⟨o.formal, .description, 0⟩ description).extend
    ⟨o.closure, .viewLogic, 0⟩ view
  (∀ premise ∈ lambdaAtoms o context, Local kernel closure premise) ∧
  ∀ invocation, kernel.admitted closure ⟨o.closure, .invocation, 0⟩ invocation →
  ∃ receipt, kernel.admitted (closure.extend ⟨o.closure, .invocation, 0⟩ invocation)
    ⟨o.formal, .receipt, 0⟩ receipt ∧
  let entry := (closure.extend ⟨o.closure, .invocation, 0⟩ invocation).extend
    ⟨o.formal, .receipt, 0⟩ receipt
  (∀ premise ∈ entryAtoms o context, Local kernel entry premise) ∧
  ∀ returned, kernel.admitted entry ⟨o.formal, .returnRebind, 0⟩ returned →
  let cut := entry.extend ⟨o.formal, .returnRebind, 0⟩ returned
  kernel.admitted cut ⟨o.formal, .shared, 0⟩ (cut.anchorValue ⟨o.formal, .shared, 0⟩) ∧
  let body := cut.extend ⟨o.formal, .shared, 0⟩ (cut.anchorValue ⟨o.formal, .shared, 0⟩)
  ∃ proof, kernel.admitted body ⟨o.body, .eventProof, 0⟩ proof ∧
  let checked := body.extend ⟨o.body, .eventProof, 0⟩ proof
  (∀ premise ∈ bodyAtoms o context, Local kernel checked premise) ∧
  (∀ premise ∈ nameAtoms o context, Local kernel checked premise)

theorem initializer_from_local_premises {Value : Type}
    (o : Occurrences) (context : Context) (kernel : Kernel Value) (environment : Environment Value)
    (premises : InitializerPremises o context kernel environment) :
    SourceJudgment kernel environment context o.initializer := by
  change Judgment kernel environment (sourceRules context o.initializer)
  rw [initializer_source_rules]
  obtain ⟨description, descriptionAdmitted, view, viewAdmitted, closureLocals, invocations⟩ := premises
  apply Judgment.existsE description descriptionAdmitted
  apply Judgment.existsE view viewAdmitted
  apply Judgment.rule closureLocals
  refine .cons (.forallE ?_) .nil
  intro invocation admitted
  obtain ⟨receipt, receiptAdmitted, entryLocals, returns⟩ := invocations invocation admitted
  apply Judgment.existsE receipt receiptAdmitted
  apply Judgment.rule entryLocals
  refine .cons (.executionOpen ?_ ?_) .nil
  · simp [Environment.extend, Binder.isEvent]
  · intro returned admitted
    obtain ⟨sharedAdmitted, proof, proofAdmitted, bodyLocals, nameLocals⟩ := returns returned admitted
    apply Judgment.sharedE sharedAdmitted
    apply Judgment.rule (by simp)
    refine .cons (.rule (by simp) .nil) (.cons ?_ .nil)
    apply Judgment.existsE proof proofAdmitted
    apply Judgment.rule bodyLocals
    exact .cons (.rule nameLocals .nil) .nil

/-- Full provider conclusion constructed from local Lambda/Shared/binding
premises and total publication coverage, without an assumed source judgment.
These local premises are uninstantiated obligations at PSR-EVENT-MAP-1. -/
theorem provider_from_total_completion {s : Sorts} {View : Type}
    (o : Occurrences) (context : Context) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (openHistory : environment.replay = none)
    (compatible : Compatible o environment inputs readout admissions)
    (initializer : InitializerPremises o context (admissionKernel inputs readout admissions original)
      (({environment with publications := totalCompletion o environment inputs readout admissions}).enterInitializer o.binding))
    (shared : ∀ returned, Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned →
      Admitted inputs readout admissions
        (returnedCut o {environment with publications := totalCompletion o environment inputs readout admissions} returned)
        o.sharedBinder
        ((returnedCut o {environment with publications := totalCompletion o environment inputs readout admissions} returned).anchorValue o.sharedBinder))
    (binding : ∀ returned, Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned →
      ∀ premise ∈ o.bindingAtoms context,
        Local (admissionKernel inputs readout admissions original)
          (completedCut o {environment with publications := totalCompletion o environment inputs readout admissions} returned) premise) :
    SourceJudgment (admissionKernel inputs readout admissions original)
      {environment with publications := totalCompletion o environment inputs readout admissions} context o.source := by
  let extended := {environment with publications := totalCompletion o environment inputs readout admissions}
  change Judgment _ extended (sourceRules context o.source)
  rw [provider_source_rules]
  apply Judgment.initializerE
  apply Judgment.rule (by simp)
  refine .cons (initializer_from_local_premises o context _ _ initializer) (.cons ?_ .nil)
  apply Judgment.executionOpen (show (extended.enterInitializer o.binding).replay = none from openHistory)
  intro returned admitted
  have originalAdmission : Admitted inputs readout admissions
      (environment.enterInitializer o.binding) o.returnBinder returned := admitted
  apply Judgment.sharedE (shared returned originalAdmission)
  apply Judgment.rule (binding returned originalAdmission)
  refine .cons ?_ .nil
  let cut := completedCut o extended returned
  apply Judgment.publishGroup (total_completion_publication_valid o environment inputs readout admissions
    compatible returned originalAdmission)
      {cut with names := [(o.providerName, publicationIdentity o environment returned)] ++ cut.names}
  · simp [Environment.publish, cut, completed_cut_candidate, extended]
    rfl
  · exact .rule (by simp) .nil

end YulangClosure.OriginalProviderPublicationCoverage
