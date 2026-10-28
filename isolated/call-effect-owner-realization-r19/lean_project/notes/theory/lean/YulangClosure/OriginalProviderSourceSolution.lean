import YulangClosure.OriginalSourceEnvironment

/-!
Provider-specific source and publication cuts for `pub id x = x`.

The incoming Context, semantic payload, original Kernel and initializer event
are deliberately not manufactured by this module. `Occurrences` is a coordinate
parameter, not an authenticated source-owner certificate. The generated trace
will be connected only at the provenance boundary. Candidate-record equations
do not install a record or prove a source judgment. Necessary conditions below
expose the fixed-map obligation of any genuine provider solution.
-/
namespace YulangClosure.OriginalProviderSourceSolution

open OriginalSource

structure Occurrences where
  binding : Site
  closure : Site
  formal : Site
  pattern : Site
  body : Site
  providerName : Name
  formalName : Name

def Occurrences.initializer (o : Occurrences) : Source .expression :=
  .lambda ⟨o.closure, none⟩ ⟨o.formal, o.formalName, none, false⟩
    (.wild o.pattern) (.name ⟨o.body, none⟩ o.formalName)

def Occurrences.source (o : Occurrences) : Source .bindings :=
  .binding o.binding o.providerName none o.initializer .bindingsNil

def Occurrences.bodyContext (o : Occurrences) (incoming : Context) : Context :=
  {name := o.formalName, owner := o.formal, kind := .formal,
    entry := some .value, singleUse := true} :: incoming

theorem body_resolves_original_formal (o : Occurrences) (incoming : Context) :
    lookupBinding (o.bodyContext incoming) o.formalName =
      some {name := o.formalName, owner := o.formal, kind := .formal, entry := some .value, singleUse := true} := by
  simp [Occurrences.bodyContext, lookupBinding]

def Occurrences.bindingAtoms (o : Occurrences) (incoming : Context) : List Premise :=
  [.atom {(atom .oneShotInitializer o.binding incoming [o.closure]) with
      names := [o.providerName]},
   .atom {(atom .publicationFinalRoot o.binding incoming [o.closure]) with
      names := [o.providerName]}]

def Occurrences.bindingTail (o : Occurrences) (incoming : Context) : RuleTree :=
  .executionE ⟨o.binding, .returnRebind, 0⟩
    (.sharedE ⟨o.binding, .shared, 0⟩
      (.rule .binding o.binding incoming (o.bindingAtoms incoming)
        (.one (.publishGroup [(o.providerName, o.binding)]
          (.rule .empty o.binding incoming [] .nil)))))

theorem provider_source_rules (o : Occurrences) (incoming : Context) :
    sourceRules incoming o.source =
      .initializerE o.binding
        (.rule .sequence o.closure incoming []
          (.two (sourceRules incoming o.initializer) (o.bindingTail incoming))) := by
  simp only [Occurrences.source, sourceRules, bindingsRulesK, expressionRulesK,
    Occurrences.initializer] <;> rfl

theorem provider_solution_requires_initializer {Value : Type}
    (o : Occurrences) (incoming : Context) (kernel : Kernel Value)
    (environment : Environment Value)
    (solution : SourceJudgment kernel environment incoming o.source) :
    SourceJudgment kernel (environment.enterInitializer o.binding) incoming o.initializer := by
  change Judgment kernel environment (sourceRules incoming o.source) at solution
  rw [provider_source_rules] at solution
  cases solution with
  | initializerE sequence =>
    cases sequence with
    | rule _ children =>
      cases children with
      | cons initializer _ => exact initializer

def Occurrences.returnBinder (o : Occurrences) : Binder := ⟨o.binding, .returnRebind, 0⟩
def Occurrences.sharedBinder (o : Occurrences) : Binder := ⟨o.binding, .shared, 0⟩

def returnedCut {Value : Type} (o : Occurrences) (incoming : Environment Value)
    (returned : ScopedValue Value) : Environment Value :=
  (incoming.enterInitializer o.binding).extend o.returnBinder returned

def completedCut {Value : Type} (o : Occurrences) (incoming : Environment Value)
    (returned : ScopedValue Value) : Environment Value :=
  let cut := returnedCut o incoming returned
  cut.extend o.sharedBinder (cut.anchorValue o.sharedBinder)

def returnFrame {Value : Type} (o : Occurrences) (incoming : Environment Value)
    (returned : ScopedValue Value) : Frame Value :=
  ⟨o.returnBinder, returned, incoming.eventPath⟩

def sharedFrame {Value : Type} (o : Occurrences) (incoming : Environment Value)
    (returned : ScopedValue Value) : Frame Value :=
  ⟨o.sharedBinder, (returnedCut o incoming returned).anchorValue o.sharedBinder,
    (returnFrame o incoming returned).exitPath⟩

def publicationIdentity {Value : Type} (o : Occurrences) (incoming : Environment Value)
    (returned : ScopedValue Value) : PublicationId Value :=
  ⟨incoming.origin, o.binding, (returnFrame o incoming returned).exitPath⟩

def publicationRecord {Value : Type} (o : Occurrences) (incoming : Environment Value)
    (returned : ScopedValue Value) : PublicationRecord Value :=
  {identity := publicationIdentity o incoming returned
   entryPath := incoming.eventPath
   entryNames := incoming.names
   entryFrames := incoming.frames.filter (fun frame => frame.binder.isFixed)
   captures := incoming.names
   fixedFrames := (incoming.frames ++
     [returnFrame o incoming returned, sharedFrame o incoming returned]).filter
       (fun frame => frame.binder.isFixed)
   initializers := ⟨o.binding, incoming.eventPath, incoming.names,
       incoming.frames.filter (fun frame => frame.binder.isFixed)⟩ :: incoming.initializers}

theorem completed_cut_retains_scope {Value : Type} (o : Occurrences)
    (incoming : Environment Value) (returned : ScopedValue Value) :
    (completedCut o incoming returned).root = incoming.root ∧
    (completedCut o incoming returned).anchors = incoming.anchors ∧
    (completedCut o incoming returned).publications = incoming.publications ∧
    (completedCut o incoming returned).names = incoming.names ∧
    (completedCut o incoming returned).frames = incoming.frames ++
      [returnFrame o incoming returned, sharedFrame o incoming returned] := by
  simp [completedCut, returnedCut, returnFrame, sharedFrame, Frame.exitPath,
    Environment.enterInitializer, Environment.extend, Occurrences.returnBinder,
    Occurrences.sharedBinder, Binder.isEvent, ActualEvent.path, List.append_assoc]

theorem completed_cut_candidate {Value : Type} (o : Occurrences)
    (incoming : Environment Value) (returned : ScopedValue Value) :
    (completedCut o incoming returned).publicationCandidate o.binding =
      some (publicationIdentity o incoming returned, publicationRecord o incoming returned) := by
  classical
  simp [Environment.publicationCandidate, Environment.prefixAtShared,
    completedCut, returnedCut, publicationIdentity, publicationRecord,
    returnFrame, sharedFrame, Frame.exitPath,
    Environment.enterInitializer, Environment.extend, Occurrences.returnBinder,
    Occurrences.sharedBinder, Binder.isEvent, Binder.isFixed, ActualEvent.path,
    List.reverse_append, List.append_assoc]

/-- Necessary fixed-map equation, extracted from an actual source solution.
This does not assume publicationValid or install a record. It does assume the
independent provider judgment, which is still an open semantic obligation. -/
theorem provider_solution_requires_fixed_record {Value : Type}
    (o : Occurrences) (incoming : Context) (kernel : Kernel Value)
    (environment : Environment Value)
    (solution : SourceJudgment kernel environment incoming o.source)
    (openHistory : environment.replay = none)
    (returned : ScopedValue Value)
    (admitted : kernel.admitted (environment.enterInitializer o.binding) o.returnBinder returned) :
    environment.publications (publicationIdentity o environment returned) =
      some (publicationRecord o environment returned) := by
  change Judgment kernel environment (sourceRules incoming o.source) at solution
  rw [provider_source_rules] at solution
  cases solution with
  | initializerE sequence =>
    cases sequence with
    | rule _ children =>
      cases children with
      | cons _ rest =>
        cases rest with
        | cons execution _ =>
          change Judgment kernel (environment.enterInitializer o.binding)
            (.executionE o.returnBinder _) at execution
          cases execution with
          | executionOpen _ branches =>
            have shared := branches returned admitted
            cases shared with
            | sharedE _ binding =>
              cases binding with
              | rule _ children =>
                cases children with
                | cons publication _ =>
                  cases publication with
                  | publishGroup valid _ _ _ =>
                    obtain ⟨identity, record, candidate, found⟩ :=
                      valid (o.providerName, o.binding) (by simp)
                    have exactCandidate := completed_cut_candidate o environment returned
                    change (completedCut o environment returned).publicationCandidate o.binding =
                      some (identity, record) at candidate
                    rw [exactCandidate] at candidate
                    have same := Option.some.inj candidate
                    have sameIdentity := congrArg Prod.fst same
                    have sameRecord := congrArg Prod.snd same
                    change publicationIdentity o environment returned = identity at sameIdentity
                    change publicationRecord o environment returned = record at sameRecord
                    change environment.publications identity = some record at found
                    rw [← sameIdentity, ← sameRecord] at found
                    exact found
          | executionFixed _ fixed _ _ _ _ =>
            simp only [Environment.enterInitializer, openHistory] at fixed
            contradiction

/-- A reused publication identity cannot designate a different complete tuple.
All fields, including captures and Shared/initializer frames, participate. -/
theorem provider_fixed_record_is_unique {Value : Type} (o : Occurrences)
    (environment : Environment Value) (returned : ScopedValue Value)
    (record : PublicationRecord Value)
    (provider : environment.publications (publicationIdentity o environment returned) =
      some (publicationRecord o environment returned))
    (reused : environment.publications (publicationIdentity o environment returned) = some record) :
    record = publicationRecord o environment returned := by
  exact Option.some.inj (reused.symm.trans provider)

/-- Original admission fixes the complete parent path. Under that original
scope condition the publication key is injective in the returned payload,
so repeated actual-event identities retain the same complete record. -/
theorem scoped_return_identity_injective {Value : Type} (o : Occurrences)
    (environment : Environment Value) (first second : ScopedValue Value)
    (firstScope : first.event.parents = environment.eventPath)
    (secondScope : second.event.parents = environment.eventPath)
    (same : publicationIdentity o environment first = publicationIdentity o environment second) :
    first = second := by
  have paths := congrArg PublicationId.path same
  change environment.eventPath ++
      [⟨o.binding, .returnRebind, first.event.occurrence, first.data⟩] =
    environment.eventPath ++
      [⟨o.binding, .returnRebind, second.event.occurrence, second.data⟩] at paths
  have steps := (List.cons.inj (List.append_cancel_left paths)).1
  have sameData := congrArg EventStep.data steps
  have sameOccurrence := congrArg EventStep.occurrence steps
  cases first with
  | mk firstData firstEvent =>
    cases second with
    | mk secondData secondEvent =>
      cases firstEvent with
      | mk firstParents firstOccurrence =>
        cases secondEvent with
        | mk secondParents secondOccurrence =>
          simp only at sameData sameOccurrence firstScope secondScope
          cases sameData
          cases sameOccurrence
          cases firstScope.trans secondScope.symm
          rfl

theorem scoped_candidates_agree {Value : Type} (o : Occurrences)
    (environment : Environment Value) (first second : ScopedValue Value)
    (firstScope : first.event.parents = environment.eventPath)
    (secondScope : second.event.parents = environment.eventPath)
    (same : publicationIdentity o environment first = publicationIdentity o environment second) :
    publicationRecord o environment first = publicationRecord o environment second := by
  exact congrArg (publicationRecord o environment)
    (scoped_return_identity_injective o environment first second firstScope secondScope same)

/-- A finite *extension* of the prior publication map, calculated from a
finite list of Return candidates. The prior map always wins. Authenticity and
coverage of this list remain with the original execution owner; HIR is not
such a list. No provider judgment is assumed in this construction. -/
noncomputable def finiteCompletion {Value : Type} (o : Occurrences)
    (environment : Environment Value) (events : List (ScopedValue Value)) :
    PublicationId Value → Option (PublicationRecord Value) := by
  classical
  exact fun identity => match environment.publications identity with
    | some record => some record
    | none => (events.find? (fun returned =>
        decide (publicationIdentity o environment returned = identity))).map
          (publicationRecord o environment)

theorem finite_completion_preserves_prior {Value : Type} (o : Occurrences)
    (environment : Environment Value) (events : List (ScopedValue Value))
    (identity : PublicationId Value) (record : PublicationRecord Value)
    (prior : environment.publications identity = some record) :
    finiteCompletion o environment events identity = some record := by
  classical
  simp only [finiteCompletion, prior]

/-- Only original parent-scope consistency and absence of an existing-record
conflict are needed for this finite data construction. Neither condition is
silently inferred from source spelling or from successful publication. -/
theorem finite_completion_contains_candidates {Value : Type} (o : Occurrences)
    (environment : Environment Value) (events : List (ScopedValue Value))
    (scopedEvents : ∀ returned ∈ events, returned.event.parents = environment.eventPath)
    (compatible : ∀ returned ∈ events, ∀ prior,
      environment.publications (publicationIdentity o environment returned) = some prior →
        prior = publicationRecord o environment returned)
    (returned : ScopedValue Value) (member : returned ∈ events) :
    finiteCompletion o environment events (publicationIdentity o environment returned) =
      some (publicationRecord o environment returned) := by
  classical
  unfold finiteCompletion
  split
  next prior found =>
    exact congrArg some (compatible returned member prior found)
  next absent =>
    cases found : events.find? (fun other =>
        decide (publicationIdentity o environment other = publicationIdentity o environment returned)) with
    | none =>
      have missing := List.find?_eq_none.mp found returned member
      simp only [decide_true] at missing
      contradiction
    | some other =>
      have otherMember := List.mem_of_find?_eq_some found
      have selected := List.find?_some (p := fun value =>
        decide (publicationIdentity o environment value = publicationIdentity o environment returned)) found
      have same : publicationIdentity o environment other = publicationIdentity o environment returned :=
        of_decide_eq_true selected
      exact congrArg some
        (scoped_candidates_agree o environment other returned
          (scopedEvents other otherMember) (scopedEvents returned member) same)

theorem finite_completion_candidate_valid {Value : Type} (o : Occurrences)
    (environment : Environment Value) (events : List (ScopedValue Value))
    (scopedEvents : ∀ returned ∈ events, returned.event.parents = environment.eventPath)
    (compatible : ∀ returned ∈ events, ∀ prior,
      environment.publications (publicationIdentity o environment returned) = some prior →
        prior = publicationRecord o environment returned)
    (returned : ScopedValue Value) (member : returned ∈ events) :
    (completedCut o {environment with publications := finiteCompletion o environment events} returned).publicationValid
      [(o.providerName, o.binding)] := by
  intro binding inBindings
  have same : binding = (o.providerName, o.binding) := by simpa using inBindings
  subst binding
  refine ⟨publicationIdentity o environment returned, publicationRecord o environment returned, ?_, ?_⟩
  · exact completed_cut_candidate o
      {environment with publications := finiteCompletion o environment events} returned
  · exact finite_completion_contains_candidates o environment events scopedEvents compatible returned member

/-- Apply the finite completion to the actual original admission interface.
Original admission supplies parent scoping; no alternate or degenerate Sorts,
admission definition, successful Kernel or source judgment is introduced. The
finite admitted event list and compatibility with old records are still open
inputs at their execution/publication owners. -/
theorem original_admitted_finite_completion
    {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (OriginalSourceEnvironment.Payload s View))
    (inputs : OriginalSourceInterpretation.Inputs s)
    (readout : OriginalSourceEnvironment.RuntimeReadout s View)
    (admissions : OriginalSourceEnvironment.LocalAdmissions s View)
    (events : List (ScopedValue (OriginalSourceEnvironment.Payload s View)))
    (admittedEvents : ∀ returned ∈ events,
      OriginalSourceEnvironment.Admitted inputs readout admissions
        (environment.enterInitializer o.binding) o.returnBinder returned)
    (compatible : ∀ returned ∈ events, ∀ prior,
      environment.publications (publicationIdentity o environment returned) = some prior →
        prior = publicationRecord o environment returned)
    (returned : ScopedValue (OriginalSourceEnvironment.Payload s View)) (member : returned ∈ events) :
    (completedCut o {environment with publications := finiteCompletion o environment events} returned).publicationValid
      [(o.providerName, o.binding)] := by
  apply finite_completion_candidate_valid o environment events _ compatible returned member
  intro value inEvents
  exact (admittedEvents value inEvents).1

/-- Decoding and original admission see the same complete semantic frame
prefix in the completed graph. This is deliberately not preservation of the
provider Judgment: its local atom/checking premises still need their owners. -/
theorem completion_preserves_original_readout
    {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (o : Occurrences) (environment : Environment (OriginalSourceEnvironment.Payload s View))
    (inputs : OriginalSourceInterpretation.Inputs s)
    (readout : OriginalSourceEnvironment.RuntimeReadout s View)
    (admissions : OriginalSourceEnvironment.LocalAdmissions s View)
    (events : List (ScopedValue (OriginalSourceEnvironment.Payload s View)))
    (binder : Binder) (candidate : ScopedValue (OriginalSourceEnvironment.Payload s View)) :
    OriginalSourceEnvironment.decode readout
      {environment with publications := finiteCompletion o environment events} =
        OriginalSourceEnvironment.decode readout environment ∧
    (OriginalSourceEnvironment.Admitted inputs readout admissions
      {environment with publications := finiteCompletion o environment events} binder candidate ↔
        OriginalSourceEnvironment.Admitted inputs readout admissions environment binder candidate) := by
  exact ⟨rfl, Iff.rfl⟩

/-- Both consumer handles retrieve exactly the original complete record.
The two handle equations are an explicit *remaining* source/import bridge;
this theorem neither constructs those equations nor identifies Rust exposure
aliasing with SRC-J Client.alias. -/
theorem complete_record_transport {Value : Type} (o : Occurrences)
    (environment : Environment Value) (returned : ScopedValue Value)
    (explicitIdentity preludeId : Name)
    (explicitExposure : environment.publicationName explicitIdentity =
      some (publicationIdentity o environment returned))
    (preludeExposure : environment.publicationName preludeId =
      some (publicationIdentity o environment returned))
    (fixedRecord : environment.publications (publicationIdentity o environment returned) =
      some (publicationRecord o environment returned)) :
    ((environment.publicationName explicitIdentity).bind environment.publications =
      some (publicationRecord o environment returned)) ∧
    ((environment.publicationName preludeId).bind environment.publications =
      some (publicationRecord o environment returned)) := by
  simp only [explicitExposure, preludeExposure, Option.bind_some, fixedRecord, and_self]

end YulangClosure.OriginalProviderSourceSolution
