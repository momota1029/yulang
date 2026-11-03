import YulangClosure.OriginalSourceEnvironmentTransportR331

/-!
R332. Apply the actual source-root inversion to the seven-binder registration.
Authority: SG §§3.3–5.2 and original source construction §§7–7.2.
No invocation or open-return domain is inhabited by this theorem. The source
judgment remains in its original kernel; cross-kernel preservation is separate.
-/
namespace YulangClosure.OriginalSourcePrefixBridgeR332
open OriginalSource OriginalScopedClosure OriginalSourceEnvironment
open OriginalSourceInterpretation OriginalInterfacePreservationR328
open OriginalSourceViewRegistrationR330 OriginalSourceEnvironmentTransportR331

variable {s : Sorts} {View : Type}

def sevenSteps (description outerView call received returned shared eventProof :
    ScopedValue (Payload s View)) : List (Binder × ScopedValue (Payload s View)) :=
  [(⟨98,.description,0⟩,description), (⟨0,.viewLogic,0⟩,outerView),
   (⟨0,.invocation,0⟩,call), (⟨98,.receipt,0⟩,received),
   (⟨98,.returnRebind,0⟩,returned), (⟨98,.shared,0⟩,shared),
   (⟨1,.eventProof,0⟩,eventProof)]

theorem seven_binders (description outerView call received returned shared eventProof :
    ScopedValue (Payload s View)) :
    (sevenSteps description outerView call received returned shared eventProof).map Prod.fst =
      selectedBinders := rfl

def RegisteredAt {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (initial reached : Environment (Payload s View)) (data : Logical s View) (occurrence : Nat) : Prop :=
  ∃ steps : List (Binder × ScopedValue (Payload s View)),
    steps.map Prod.fst = selectedBinders ∧
    PrefixAdmitted base ro adm initial steps ∧
    reached = runPrefix initial steps ∧
    PrefixAdmitted (inputs base gen) (readout definition.code ro) (admissions definition.code adm)
      (environment definition.code initial) (prefixImage definition.code steps) ∧
    (decode (readout definition.code ro)
      ((environment definition.code reached).extend (owner origin).binder
        (scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)))).map
      (fun after => after.viewMeaning (.inr ())) = some (.inr definition.code)

def SelectedRegistered {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (kernel : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View))
    (data : Logical s View) (occurrence : Nat) : Prop :=
  let b : Binder := ⟨98,.shared,0⟩
  let shared := beforeShared.anchorValue b
  let after := beforeShared.extend b shared
  kernel.admitted beforeShared b shared ∧ ∃ eventProof,
    kernel.admitted after ⟨1,.eventProof,0⟩ eventProof ∧
    SourceJudgment kernel (after.extend ⟨1,.eventProof,0⟩ eventProof) selectedContext selectedSource ∧
    RegisteredAt definition base gen ro adm initial
      (after.extend ⟨1,.eventProof,0⟩ eventProof) data occurrence

theorem register_selected_continuation
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial : Environment (Payload s View))
    (state : Decoded s View) (found : decode ro initial = some state)
    (description outerView call received returned : ScopedValue (Payload s View))
    (data : Logical s View) (occurrence : Nat)
    (hDescription : Admitted base ro adm initial ⟨98,.description,0⟩ description)
    (hView : Admitted base ro adm (initial.extend ⟨98,.description,0⟩ description) ⟨0,.viewLogic,0⟩ outerView)
    (hCall : Admitted base ro adm
      ((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView) ⟨0,.invocation,0⟩ call)
    (hReceived : Admitted base ro adm
      (((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView).extend
        ⟨0,.invocation,0⟩ call) ⟨98,.receipt,0⟩ received)
    (hReturned : Admitted base ro adm
      ((((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView).extend
        ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received) ⟨98,.returnRebind,0⟩ returned)
    (continuation : SelectedContinuation (admissionKernel base ro adm original)
      (((((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView).extend
        ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received).extend ⟨98,.returnRebind,0⟩ returned)) :
    SelectedRegistered definition base gen ro adm (admissionKernel base ro adm original) initial
      (((((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView).extend
        ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received).extend ⟨98,.returnRebind,0⟩ returned)
      data occurrence := by
  obtain ⟨hShared, eventProof, hEvent, source⟩ := continuation
  refine ⟨hShared, eventProof, hEvent, source, ?_⟩
  let before := ((((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView).extend
      ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received).extend ⟨98,.returnRebind,0⟩ returned
  let shared := before.anchorValue ⟨98,.shared,0⟩
  let steps := sevenSteps description outerView call received returned shared eventProof
  have accepted : PrefixAdmitted base ro adm initial steps :=
    ⟨hDescription,hView,hCall,hReceived,hReturned,hShared,hEvent,True.intro⟩
  have registered := selected_prefix_registration definition base gen ro adm initial state found
    steps (seven_binders ..) accepted data occurrence
  refine ⟨steps, seven_binders .., accepted, rfl, registered.2.1, ?_⟩
  have final := registered.2.2.2
  rw [← prefix_commutes] at final
  exact final

def ReturnRegistered {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (kernel : Kernel (Payload s View)) (initial beforeReturn : Environment (Payload s View))
    (data : Logical s View) (occurrence : Nat) : Prop :=
  let b : Binder := ⟨98,.returnRebind,0⟩
  match beforeReturn.replay with
  | none => ∀ returned, kernel.admitted beforeReturn b returned →
      SelectedRegistered definition base gen ro adm kernel initial (beforeReturn.extend b returned) data occurrence
  | some _ => ∃ returned, beforeReturn.executionValue b = some returned ∧
      kernel.admitted beforeReturn b returned ∧
      SelectedRegistered definition base gen ro adm kernel initial (beforeReturn.extend b returned) data occurrence

/-- The original source derivation supplies every prefix admission used by
R330 registration, with the same selected source proof. Open executions retain
all admitted returns; fixed executions retain their actual saved lookup. -/
theorem original_source_registered_alternatives
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial : Environment (Payload s View))
    (state : Decoded s View) (found : decode ro initial = some state)
    (data : Logical s View) (occurrence : Nat)
    (sourceProof : SourceJudgment (admissionKernel base ro adm original) initial
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root) :
    ∃ description outerView,
      Admitted base ro adm initial ⟨98,.description,0⟩ description ∧
      let afterDescription := initial.extend ⟨98,.description,0⟩ description
      Admitted base ro adm afterDescription ⟨0,.viewLogic,0⟩ outerView ∧
      let afterView := afterDescription.extend ⟨0,.viewLogic,0⟩ outerView
      ∀ call, Admitted base ro adm afterView ⟨0,.invocation,0⟩ call →
        let afterCall := afterView.extend ⟨0,.invocation,0⟩ call
        ∃ received, Admitted base ro adm afterCall ⟨98,.receipt,0⟩ received ∧
          ReturnRegistered definition base gen ro adm (admissionKernel base ro adm original) initial
            (afterCall.extend ⟨98,.receipt,0⟩ received) data occurrence := by
  obtain ⟨description, outerView, hDescription, hView, calls⟩ :=
    original_source_prefix_alternatives (admissionKernel base ro adm original) initial sourceProof
  refine ⟨description,outerView,hDescription,hView,?_⟩
  dsimp only
  intro call hCall
  obtain ⟨received,hReceived,returns⟩ := calls call hCall
  refine ⟨received,hReceived,?_⟩
  let beforeReturn := (((initial.extend ⟨98,.description,0⟩ description).extend
    ⟨0,.viewLogic,0⟩ outerView).extend ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received
  change ReturnContinuations (admissionKernel base ro adm original) beforeReturn at returns
  cases replay : beforeReturn.replay with
  | none =>
    change ReturnRegistered definition base gen ro adm _ initial beforeReturn data occurrence
    simp only [ReturnRegistered, replay]
    have openReturns : ∀ returned, Admitted base ro adm beforeReturn ⟨98,.returnRebind,0⟩ returned →
        SelectedContinuation (admissionKernel base ro adm original)
          (beforeReturn.extend ⟨98,.returnRebind,0⟩ returned) := by
      simpa only [ReturnContinuations, replay, admissionKernel] using returns
    intro returned hReturned
    exact register_selected_continuation definition base gen ro adm original initial state found
      description outerView call received returned data occurrence hDescription hView hCall hReceived hReturned
      (openReturns returned hReturned)
  | some history =>
    change ReturnRegistered definition base gen ro adm _ initial beforeReturn data occurrence
    simp only [ReturnRegistered, replay]
    have fixedReturns : ∃ returned, beforeReturn.executionValue ⟨98,.returnRebind,0⟩ = some returned ∧
        Admitted base ro adm beforeReturn ⟨98,.returnRebind,0⟩ returned ∧
        SelectedContinuation (admissionKernel base ro adm original)
          (beforeReturn.extend ⟨98,.returnRebind,0⟩ returned) := by
      simpa only [ReturnContinuations, replay, admissionKernel] using returns
    obtain ⟨returned,lookup,hReturned,continuation⟩ := fixedReturns
    exact ⟨returned,lookup,hReturned,
      register_selected_continuation definition base gen ro adm original initial state found
        description outerView call received returned data occurrence hDescription hView hCall hReceived hReturned
        continuation⟩

theorem actual_candidate_image
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (reached : Environment (Payload s View))
    (data : Logical s View) (occurrence : Nat) :
    scopedValue definition.code (scopeCandidate reached occurrence (.logical .viewLogic data)) =
      scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition) := rfl

theorem actual_parent_extension_image
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (reached : Environment (Payload s View))
    (data : Logical s View) (occurrence : Nat) :
    environment definition.code (reached.extend (owner origin).binder
      (scopeCandidate reached occurrence (.logical .viewLogic data))) =
      (environment definition.code reached).extend (owner origin).binder
        (scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)) := by
  rw [extension_commutes, actual_candidate_image]

def ParentRegisteredAt
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial reached : Environment (Payload s View)) : Prop :=
  let kernel := admissionKernel base ro adm original
  let mark : Mark := ⟨1,none⟩
  let callee := OriginalScopedSourceEventMapR314.Fixture.callee
  let argument := OriginalScopedSourceEventMapR314.Fixture.argument
  (∀ premise ∈ SourceAppAdmissionR159.annotationPremises selectedContext mark,
    Local kernel reached premise) ∧
  ∃ occurrence data state,
    decode ro reached = some state ∧
    adm.logical state ⟨1,.viewLogic,0⟩ .viewLogic data ∧
    let candidate := scopeCandidate reached occurrence (.logical .viewLogic data)
    let after := reached.extend ⟨1,.viewLogic,0⟩ candidate
    original.atom after (atom .descriptorFormation 1 selectedContext [callee.site,argument.site]) ∧
    (∀ premise ∈ OriginalSourceContractResolutionR311.remainingPremises selectedContext mark callee argument,
      Local kernel after premise) ∧
    SourceJudgment kernel after selectedContext callee ∧
    SourceJudgment kernel after selectedContext argument ∧
    RegisteredAt definition base gen ro adm initial reached data occurrence ∧
    environment definition.code after =
      (environment definition.code reached).extend (owner origin).binder
        (scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)) ∧
    Admitted (inputs base gen) (readout definition.code ro) (admissions definition.code adm)
      (environment definition.code reached) (owner origin).binder
      (scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition))

/-- Use the actual original parent witnesses, not caller-selected logical data.
Its original admission proves admission of the corresponding generated payload
in the conservative transported instance. All original parent fields and both
children remain at their identical original extension. -/
theorem register_actual_parent
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial reached : Environment (Payload s View))
    (initialState : Decoded s View) (initialFound : decode ro initial = some initialState)
    (priorData : Logical s View) (priorOccurrence : Nat)
    (registered : RegisteredAt definition base gen ro adm initial reached priorData priorOccurrence)
    (source : SourceJudgment (admissionKernel base ro adm original) reached selectedContext selectedSource) :
    ParentRegisteredAt definition base gen ro adm original initial reached := by
  have parent := (OriginalModuleContextBindingR315.original_parent_formation_iff
    base ro adm original reached).mp source
  obtain ⟨annotations, occurrence, data, state, found, admitted, formation, locals, callee, argument⟩ := parent
  obtain ⟨steps,binders,accepted,reachedEq,_⟩ := registered
  refine ⟨annotations,occurrence,data,state,found,admitted,formation,locals,callee,argument,?_,?_,?_⟩
  · have now := selected_prefix_registration definition base gen ro adm initial initialState initialFound
      steps binders accepted data occurrence
    refine ⟨steps,binders,accepted,reachedEq,now.2.1,?_⟩
    have final := now.2.2.2
    rw [← prefix_commutes, ← reachedEq] at final
    exact final
  · exact actual_parent_extension_image definition reached data occurrence
  · exact (original_parent_admission definition base gen ro adm reached state found data occurrence).mpr admitted

def SelectedParentRegistered
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View)) : Prop :=
  let kernel := admissionKernel base ro adm original
  let b : Binder := ⟨98,.shared,0⟩
  let shared := beforeShared.anchorValue b
  let after := beforeShared.extend b shared
  kernel.admitted beforeShared b shared ∧ ∃ eventProof,
    kernel.admitted after ⟨1,.eventProof,0⟩ eventProof ∧
    SourceJudgment kernel (after.extend ⟨1,.eventProof,0⟩ eventProof) selectedContext selectedSource ∧
    ParentRegisteredAt definition base gen ro adm original initial
      (after.extend ⟨1,.eventProof,0⟩ eventProof)

theorem selected_registered_actual_parent
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View))
    (initialState : Decoded s View) (initialFound : decode ro initial = some initialState)
    (priorData : Logical s View) (priorOccurrence : Nat)
    (registered : SelectedRegistered definition base gen ro adm (admissionKernel base ro adm original)
      initial beforeShared priorData priorOccurrence) :
    SelectedParentRegistered definition base gen ro adm original initial beforeShared := by
  obtain ⟨hShared,eventProof,hEvent,source,registration⟩ := registered
  exact ⟨hShared,eventProof,hEvent,source,
    register_actual_parent definition base gen ro adm original initial _ initialState initialFound
      priorData priorOccurrence registration source⟩

def ReturnParentRegistered
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial beforeReturn : Environment (Payload s View)) : Prop :=
  let kernel := admissionKernel base ro adm original
  let b : Binder := ⟨98,.returnRebind,0⟩
  match beforeReturn.replay with
  | none => ∀ returned, kernel.admitted beforeReturn b returned →
      SelectedParentRegistered definition base gen ro adm original initial (beforeReturn.extend b returned)
  | some _ => ∃ returned, beforeReturn.executionValue b = some returned ∧
      kernel.admitted beforeReturn b returned ∧
      SelectedParentRegistered definition base gen ro adm original initial (beforeReturn.extend b returned)

theorem return_registered_actual_parent
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial beforeReturn : Environment (Payload s View))
    (initialState : Decoded s View) (initialFound : decode ro initial = some initialState)
    (priorData : Logical s View) (priorOccurrence : Nat)
    (registered : ReturnRegistered definition base gen ro adm (admissionKernel base ro adm original)
      initial beforeReturn priorData priorOccurrence) :
    ReturnParentRegistered definition base gen ro adm original initial beforeReturn := by
  cases replay : beforeReturn.replay with
  | none =>
    simp only [ReturnRegistered,replay] at registered
    simp only [ReturnParentRegistered,replay]
    intro returned hReturned
    exact selected_registered_actual_parent definition base gen ro adm original initial _ initialState
      initialFound priorData priorOccurrence (registered returned hReturned)
  | some history =>
    simp only [ReturnRegistered,replay] at registered
    simp only [ReturnParentRegistered,replay]
    obtain ⟨returned,lookup,hReturned,selected⟩ := registered
    exact ⟨returned,lookup,hReturned,
      selected_registered_actual_parent definition base gen ro adm original initial _ initialState
        initialFound priorData priorOccurrence selected⟩

theorem register_selected_original_parent
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View))
    (initialState : Decoded s View) (initialFound : decode ro initial = some initialState)
    (continuation : SelectedContinuation (admissionKernel base ro adm original) beforeShared)
    (register : ∀ data occurrence,
      SelectedRegistered definition base gen ro adm (admissionKernel base ro adm original)
        initial beforeShared data occurrence) :
    SelectedParentRegistered definition base gen ro adm original initial beforeShared := by
  obtain ⟨_,eventProof,_,source⟩ := continuation
  obtain ⟨_,occurrence,data,_⟩ := (OriginalModuleContextBindingR315.original_parent_formation_iff
    base ro adm original _).mp source
  exact selected_registered_actual_parent definition base gen ro adm original initial beforeShared
    initialState initialFound data occurrence (register data occurrence)

/-- Applied original R315/R159 parent inversion along the actual source root.
The witnessed old logical law supplies the generated candidate's transported
admission; no admission, invocation, return or source child is invented. -/
theorem original_source_parent_registered_alternatives
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial : Environment (Payload s View))
    (state : Decoded s View) (found : decode ro initial = some state)
    (sourceProof : SourceJudgment (admissionKernel base ro adm original) initial
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root) :
    ∃ description outerView,
      Admitted base ro adm initial ⟨98,.description,0⟩ description ∧
      let afterDescription := initial.extend ⟨98,.description,0⟩ description
      Admitted base ro adm afterDescription ⟨0,.viewLogic,0⟩ outerView ∧
      let afterView := afterDescription.extend ⟨0,.viewLogic,0⟩ outerView
      ∀ call, Admitted base ro adm afterView ⟨0,.invocation,0⟩ call →
        let afterCall := afterView.extend ⟨0,.invocation,0⟩ call
        ∃ received, Admitted base ro adm afterCall ⟨98,.receipt,0⟩ received ∧
          ReturnParentRegistered definition base gen ro adm original initial
            (afterCall.extend ⟨98,.receipt,0⟩ received) := by
  obtain ⟨description,outerView,hDescription,hView,calls⟩ :=
    original_source_prefix_alternatives (admissionKernel base ro adm original) initial sourceProof
  refine ⟨description,outerView,hDescription,hView,?_⟩
  dsimp only
  intro call hCall
  obtain ⟨received,hReceived,returns⟩ := calls call hCall
  refine ⟨received,hReceived,?_⟩
  let beforeReturn := (((initial.extend ⟨98,.description,0⟩ description).extend
    ⟨0,.viewLogic,0⟩ outerView).extend ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received
  change ReturnContinuations (admissionKernel base ro adm original) beforeReturn at returns
  have register : ∀ returned,
      Admitted base ro adm beforeReturn ⟨98,.returnRebind,0⟩ returned →
      SelectedContinuation (admissionKernel base ro adm original)
        (beforeReturn.extend ⟨98,.returnRebind,0⟩ returned) →
      SelectedParentRegistered definition base gen ro adm original initial
        (beforeReturn.extend ⟨98,.returnRebind,0⟩ returned) := by
    intro returned hReturned continuation
    apply register_selected_original_parent definition base gen ro adm original initial _ state found continuation
    intro data occurrence
    exact register_selected_continuation definition base gen ro adm original initial state found
      description outerView call received returned data occurrence hDescription hView hCall hReceived hReturned continuation
  cases replay : beforeReturn.replay with
  | none =>
    change ReturnParentRegistered definition base gen ro adm original initial beforeReturn
    simp only [ReturnParentRegistered,replay]
    simp only [ReturnContinuations,replay] at returns
    intro returned hReturned
    exact register returned hReturned (returns returned hReturned)
  | some history =>
    change ReturnParentRegistered definition base gen ro adm original initial beforeReturn
    simp only [ReturnParentRegistered,replay]
    simp only [ReturnContinuations,replay] at returns
    obtain ⟨returned,lookup,hReturned,continuation⟩ := returns
    exact ⟨returned,lookup,hReturned,register returned hReturned continuation⟩

end YulangClosure.OriginalSourcePrefixBridgeR332
