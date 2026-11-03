import YulangClosure.OriginalSourceKernelTransportR333

/-!
R333 repair: transport the actual current-goal checking kernel. This uses
`goalFunctionKernel` in BOTH source and target, including the independently
defined FunctionShape. Goal admission is never identified with source admission.

Authority: SG §§3.1–3.3, SRC §6, and OriginalCheckingAdmission's corrected
current-goal domain. All remaining primitive relations are conservative images
of their original evidence. Native authentication of those relations is open.
-/
namespace YulangClosure.OriginalSourceGoalKernelTransportR333
open OriginalSource OriginalScopedClosure OriginalSourceEnvironment
open OriginalSourceInterpretation OriginalInterfacePreservationR328
open OriginalSourceViewRegistrationR330 OriginalSourceEnvironmentTransportR331
open OriginalSourcePrefixBridgeR332 OriginalCheckingAdmission
open OriginalSourceAdmittedImageR333 OriginalSourcePublicationTransportR333
open OriginalSourceKernelTransportR333 (primitiveKernel atom_transport primitive_transport
  structural_transport boundaryTag_transport conversion_transport)

variable {s : Sorts} {View G : Type}

/-- The exact original goal-indexed Function wrapper, applied after the
conservative image of the other independently supplied primitive relations. -/
noncomputable def transportedKernel (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) : Kernel (Payload (extended s G) (Sum View Unit)) :=
  goalFunctionKernel (inputs base gen) (readout g ro) (admissions g adm) (primitiveKernel g old)

/-- Genuine Function incidence is preserved, rather than transporting an
arbitrary old functionShape predicate and calling it FunctionShape. -/
theorem function_shape_preserved (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (env : Environment (Payload s View))
    (goal domain : CheckGoal) (binder : Binder) (observation : CheckGoal)
    (shape : OriginalSourceEnvironment.FunctionShape base ro env goal domain binder observation) :
    OriginalSourceEnvironment.FunctionShape (inputs base gen) (readout g ro)
      (environment g env) goal domain binder observation := by
  obtain ⟨mode,domainMode,observationMode,kind,owner,domainLower,domainUpper,
    observationLower,observationUpper,domainContext,observationContext,state,found,
    registered,lowerForm,upperForm⟩ := shape
  refine ⟨mode,domainMode,observationMode,kind,owner,domainLower,domainUpper,
    observationLower,observationUpper,domainContext,observationContext,
    decoded g state,?_,?_,lowerForm,upperForm⟩
  · rw [decode_commutes,found]; rfl
  · exact registered

/-- Function observations quantify over every actually admitted target
candidate. The exact image theorem supplies its original preimage. -/
theorem checking_transport (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) {env : Environment (Payload s View)} {goal : CheckGoal}
    (checked : Checking (goalFunctionKernel base ro adm old) env goal) :
    Checking (transportedKernel g base gen ro adm old) (environment g env) goal := by
  refine Checking.rec
    (motive_1 := fun env goal _ => Checking (transportedKernel g base gen ro adm old) (environment g env) goal)
    (motive_2 := fun env children _ => Checkings (transportedKernel g base gen ro adm old) (environment g env) children)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ checked
  · intro env goal same
    exact .identity goal same
  · intro env goal declaration valid
    exact .primitive goal declaration (primitive_transport g old env declaration goal valid)
  · intro env mode site context first middle last left right leftIH rightIH
    exact .compose mode site context first middle last leftIH rightIH
  · intro env rule goal children shape checked childrenIH
    exact .structural rule goal children (structural_transport g old env rule goal children shape) childrenIH
  · intro env goal domain observation binder domainMode observationMode invocation shape domainProof observationProof domainIH observationIH
    refine .function goal domain observation binder domainMode observationMode invocation
      (function_shape_preserved g base gen ro env goal domain binder observation shape) domainIH ?_
    intro candidate valid
    obtain ⟨original, rfl, admitted⟩ := (goal_admitted_image_iff g base gen ro adm env goal binder candidate).mp valid
    rw [← extension_commutes]
    exact observationIH original admitted
  · intro env
    exact .nil
  · intro env head tail first rest firstIH restIH
    exact .cons firstIH restIH

theorem boundary_transport (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) {env : Environment (Payload s View)}
    {site : Site} {context : Context} {lower upper : Endpoint}
    (proof : Boundary (goalFunctionKernel base ro adm old) env site context lower upper) :
    Boundary (transportedKernel g base gen ro adm old) (environment g env) site context lower upper := by
  cases proof with
  | proofOnly mode sourceTag checked =>
    exact .proofOnly site context lower upper mode
      (boundaryTag_transport g old env site context lower upper mode sourceTag)
      (checking_transport g base gen ro adm old checked)
  | actual declaration valid =>
    exact .actual site context lower upper declaration
      (conversion_transport g old env site context lower upper declaration valid)

theorem local_transport (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) {env : Environment (Payload s View)} {premise : Premise}
    (proof : Local (goalFunctionKernel base ro adm old) env premise) :
    Local (transportedKernel g base gen ro adm old) (environment g env) premise := by
  cases proof with
  | atom valid => exact .atom (atom_transport g old env _ valid)
  | checking checked => exact .checking (checking_transport g base gen ro adm old checked)
  | boundary checked => exact .boundary (boundary_transport g base gen ro adm old checked)

/-- All source-rule constructors, including open/fixed execution, shared
anchors and all three publication operations, transport at one environment.
Neither universal case assumes its target candidate is already an image. -/
theorem judgment_transport (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) {env : Environment (Payload s View)} {tree : RuleTree}
    (proof : Judgment (goalFunctionKernel base ro adm old) env tree) :
    Judgment (transportedKernel g base gen ro adm old) (environment g env) tree := by
  refine Judgment.rec
    (motive_1 := fun env tree _ => Judgment (transportedKernel g base gen ro adm old) (environment g env) tree)
    (motive_2 := fun env trees _ => Judgments (transportedKernel g base gen ro adm old) (environment g env) trees)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro env rule site context premises children locals childrenProof childrenIH
    exact .rule (fun premise member => local_transport g base gen ro adm old (locals premise member)) childrenIH
  · intro env binder body value valid proof ih
    refine .existsE (scopedValue g value) ((admission_preserved g base gen ro adm env binder value).mpr valid) ?_
    rw [← extension_commutes]
    exact ih
  · intro env binder body proof ih
    apply Judgment.forallE
    intro candidate valid
    obtain ⟨original, rfl, admitted⟩ := (admitted_image_iff g base gen ro adm env binder candidate).mp valid
    rw [← extension_commutes]
    exact ih original admitted
  · intro env site body proof ih
    apply Judgment.initializerE
    rw [← initializer_commutes]
    exact ih
  · intro env binder body openHistory proof ih
    apply Judgment.executionOpen
    · change env.replay.map (List.map (frame g)) = none
      rw [openHistory]; rfl
    · intro candidate valid
      obtain ⟨original, rfl, admitted⟩ := (admitted_image_iff g base gen ro adm env binder candidate).mp valid
      rw [← extension_commutes]
      exact ih original admitted
  · intro env binder body history fixedHistory value lookup valid proof ih
    refine Judgment.executionFixed (history.map (frame g)) ?_ (scopedValue g value) ?_
      ((admission_preserved g base gen ro adm env binder value).mpr valid) ?_
    · change env.replay.map (List.map (frame g)) = some (history.map (frame g))
      rw [fixedHistory]; rfl
    · rw [executionValue_preserved, lookup]; rfl
    · rw [← extension_commutes]
      exact ih
  · intro env binder body valid proof ih
    apply Judgment.sharedE
    · rw [anchorValue_preserved]
      exact (admission_preserved g base gen ro adm env binder (env.anchorValue binder)).mpr valid
    · rw [anchorValue_preserved, ← extension_commutes]
      exact ih
  · intro env bindings body valid next constructed proof ih
    refine Judgment.publishGroup ((publicationValid_iff g env bindings).mpr valid) (environment g next) ?_ ih
    rw [publish_commutes, constructed]; rfl
  · intro env name body restored lookup proof ih
    refine Judgment.atPublication (environment g restored) ?_ ih
    rw [atPublication_commutes, lookup]; rfl
  · intro env original aliasName body aliased lookup proof ih
    refine Judgment.aliasPublication (environment g aliased) ?_ ih
    rw [aliasPublication_commutes, lookup]; rfl
  · intro env site left right proof ih
    exact .chooseLeft ih
  · intro env site left right proof ih
    exact .chooseRight ih
  · intro env
    exact .nil
  · intro env head tail first rest firstIH restIH
    exact .cons firstIH restIH

/-- The source program is computed from the unchanged original source. -/
theorem source_transport (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) {env : Environment (Payload s View)}
    (context : Context) {category : Category} (source : Source category)
    (proof : SourceJudgment (goalFunctionKernel base ro adm old) env context source) :
    SourceJudgment (transportedKernel g base gen ro adm old) (environment g env) context source :=
  judgment_transport g base gen ro adm old proof

/-- R159/R315 formation inversion with the ACTUAL goal-indexed kernel.
The same candidate extension carries all locals and both children. Both outer
annotation alternatives and the optional singleton-formal premise are kept. -/
theorem app_parent_formation_iff (base : Inputs s) (ro : RuntimeReadout s View)
    (adm : LocalAdmissions s View) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    let kernel := goalFunctionKernel base ro adm old
    SourceJudgment kernel env context (.app mark callee argument) ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel env premise) ∧
      ∃ occurrence data state,
        decode ro env = some state ∧
        adm.logical state ⟨mark.site,.viewLogic,0⟩ .viewLogic data ∧
        let after := env.extend ⟨mark.site,.viewLogic,0⟩
          (scopeCandidate env occurrence (.logical .viewLogic data))
        old.atom after (atom .descriptorFormation mark.site context [callee.site,argument.site]) ∧
        (∀ premise ∈ OriginalSourceContractResolutionR311.remainingPremises context mark callee argument,
          Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧ SourceJudgment kernel after context argument := by
  dsimp only
  rw [SourceAppAdmissionR159.app_source_iff]
  constructor
  · rintro ⟨annotations,candidate,valid,body⟩
    obtain ⟨occurrence,data,state,rfl,found,admitted⟩ :=
      (SourceAppAdmissionR159.admitted_view_iff base ro adm env mark.site candidate).mp valid
    obtain ⟨locals,first,second⟩ :=
      (SourceAppAdmissionR159.app_continuation_iff _ _ context mark callee argument).mp body
    rw [OriginalSourceContractResolutionR311.original_premises_cons] at locals
    have formed := locals _ List.mem_cons_self
    cases formed with
    | atom formed =>
      exact ⟨annotations,occurrence,data,state,found,admitted,formed,
        fun premise member => locals premise (List.mem_cons_of_mem _ member),first,second⟩
  · rintro ⟨annotations,occurrence,data,state,found,admitted,formed,locals,first,second⟩
    refine ⟨annotations,scopeCandidate env occurrence (.logical .viewLogic data),?_,?_⟩
    · exact (SourceAppAdmissionR159.admitted_view_iff base ro adm env mark.site _).mpr
        ⟨occurrence,data,state,rfl,found,admitted⟩
    · apply (SourceAppAdmissionR159.app_continuation_iff _ _ context mark callee argument).mpr
      refine ⟨?_,first,second⟩
      rw [OriginalSourceContractResolutionR311.original_premises_cons]
      intro premise member
      rcases List.mem_cons.mp member with same | member
      · subst premise; exact .atom formed
      · exact locals premise member

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
    (continuation : SelectedContinuation (goalFunctionKernel base ro adm original)
      (((((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView).extend
        ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received).extend ⟨98,.returnRebind,0⟩ returned)) :
    SelectedRegistered definition base gen ro adm (goalFunctionKernel base ro adm original) initial
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

def ParentRegisteredAt
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial reached : Environment (Payload s View)) : Prop :=
  let kernel := goalFunctionKernel base ro adm original
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
    (source : SourceJudgment (goalFunctionKernel base ro adm original) reached selectedContext selectedSource) :
    ParentRegisteredAt definition base gen ro adm original initial reached := by
  have parent := (app_parent_formation_iff
    base ro adm original reached selectedContext ⟨1,none⟩
    OriginalScopedSourceEventMapR314.Fixture.callee OriginalScopedSourceEventMapR314.Fixture.argument).mp source
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
  let kernel := goalFunctionKernel base ro adm original
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
    (registered : SelectedRegistered definition base gen ro adm (goalFunctionKernel base ro adm original)
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
  let kernel := goalFunctionKernel base ro adm original
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
    (registered : ReturnRegistered definition base gen ro adm (goalFunctionKernel base ro adm original)
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
    (continuation : SelectedContinuation (goalFunctionKernel base ro adm original) beforeShared)
    (register : ∀ data occurrence,
      SelectedRegistered definition base gen ro adm (goalFunctionKernel base ro adm original)
        initial beforeShared data occurrence) :
    SelectedParentRegistered definition base gen ro adm original initial beforeShared := by
  obtain ⟨_,eventProof,_,source⟩ := continuation
  obtain ⟨_,occurrence,data,_⟩ := (app_parent_formation_iff
    base ro adm original _ selectedContext ⟨1,none⟩
    OriginalScopedSourceEventMapR314.Fixture.callee OriginalScopedSourceEventMapR314.Fixture.argument).mp source
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
    (sourceProof : SourceJudgment (goalFunctionKernel base ro adm original) initial
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
    original_source_prefix_alternatives (goalFunctionKernel base ro adm original) initial sourceProof
  refine ⟨description,outerView,hDescription,hView,?_⟩
  dsimp only
  intro call hCall
  obtain ⟨received,hReceived,returns⟩ := calls call hCall
  refine ⟨received,hReceived,?_⟩
  let beforeReturn := (((initial.extend ⟨98,.description,0⟩ description).extend
    ⟨0,.viewLogic,0⟩ outerView).extend ⟨0,.invocation,0⟩ call).extend ⟨98,.receipt,0⟩ received
  change ReturnContinuations (goalFunctionKernel base ro adm original) beforeReturn at returns
  have register : ∀ returned,
      Admitted base ro adm beforeReturn ⟨98,.returnRebind,0⟩ returned →
      SelectedContinuation (goalFunctionKernel base ro adm original)
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

/-- R332's original witness and registration, with all R159 premises and both
source children at the SAME generated-candidate extension. -/
def ParentTransportedAt
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial reached : Environment (Payload s View)) : Prop :=
  let kernel := transportedKernel definition.code base gen ro adm old
  let before := environment definition.code reached
  let mark : Mark := ⟨1,none⟩
  let callee := OriginalScopedSourceEventMapR314.Fixture.callee
  let argument := OriginalScopedSourceEventMapR314.Fixture.argument
  (∀ premise ∈ SourceAppAdmissionR159.annotationPremises selectedContext mark,
    Local kernel before premise) ∧
  ∃ occurrence data state,
    decode ro reached = some state ∧
    adm.logical state ⟨1,.viewLogic,0⟩ .viewLogic data ∧
    RegisteredAt definition base gen ro adm initial reached data occurrence ∧
    let candidate := scopeCandidate before occurrence (definedPayload data definition)
    let after := before.extend ⟨1,.viewLogic,0⟩ candidate
    environment definition.code
      (reached.extend ⟨1,.viewLogic,0⟩ (scopeCandidate reached occurrence (.logical .viewLogic data))) = after ∧
    kernel.admitted before ⟨1,.viewLogic,0⟩ candidate ∧
    kernel.atom after (atom .descriptorFormation 1 selectedContext [callee.site,argument.site]) ∧
    (∀ premise ∈ OriginalSourceContractResolutionR311.remainingPremises selectedContext mark callee argument,
      Local kernel after premise) ∧
    SourceJudgment kernel after selectedContext callee ∧
    SourceJudgment kernel after selectedContext argument ∧
    SourceJudgment kernel before selectedContext selectedSource

/-- Apply the complete transport to the actual parent witnesses supplied by
R332. Original logical admission and registration are retained, while the
previously missing local/child cross-kernel obligations are constructed. -/
theorem registered_parent_transport
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial reached : Environment (Payload s View))
    (parent : ParentRegisteredAt definition base gen ro adm old initial reached) :
    ParentTransportedAt definition base gen ro adm old initial reached := by
  obtain ⟨annotations,occurrence,data,state,found,admitted,formation,locals,callee,argument,
    registered,extension,imageAdmitted⟩ := parent
  change _ = (environment definition.code reached).extend ⟨1,.viewLogic,0⟩
    (scopeCandidate (environment definition.code reached) occurrence (definedPayload data definition)) at extension
  refine ⟨?_,occurrence,data,state,found,admitted,registered,extension,imageAdmitted,?_,?_,?_,?_,?_⟩
  · intro premise member
    exact local_transport definition.code base gen ro adm old (annotations premise member)
  · rw [← extension]
    exact atom_transport definition.code old _ _ formation
  · intro premise member
    rw [← extension]
    exact local_transport definition.code base gen ro adm old (locals premise member)
  · rw [← extension]
    exact source_transport definition.code base gen ro adm old selectedContext _ callee
  · rw [← extension]
    exact source_transport definition.code base gen ro adm old selectedContext _ argument
  · apply source_transport definition.code base gen ro adm old selectedContext selectedSource
    apply (app_parent_formation_iff base ro adm old reached selectedContext ⟨1,none⟩
      OriginalScopedSourceEventMapR314.Fixture.callee OriginalScopedSourceEventMapR314.Fixture.argument).mpr
    exact ⟨annotations,occurrence,data,state,found,admitted,formation,locals,callee,argument⟩

theorem register_actual_parent_transport
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial reached : Environment (Payload s View))
    (initialState : Decoded s View) (initialFound : decode ro initial = some initialState)
    (priorData : Logical s View) (priorOccurrence : Nat)
    (registered : RegisteredAt definition base gen ro adm initial reached priorData priorOccurrence)
    (source : SourceJudgment (goalFunctionKernel base ro adm old) reached selectedContext selectedSource) :
    ParentTransportedAt definition base gen ro adm old initial reached :=
  registered_parent_transport definition base gen ro adm old initial reached
    (register_actual_parent definition base gen ro adm old initial reached initialState initialFound
      priorData priorOccurrence registered source)

def SelectedParentTransported
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View)) : Prop :=
  let kernel := goalFunctionKernel base ro adm old
  let b : Binder := ⟨98,.shared,0⟩
  let shared := beforeShared.anchorValue b
  let after := beforeShared.extend b shared
  kernel.admitted beforeShared b shared ∧ ∃ eventProof,
    kernel.admitted after ⟨1,.eventProof,0⟩ eventProof ∧
    ParentTransportedAt definition base gen ro adm old initial
      (after.extend ⟨1,.eventProof,0⟩ eventProof)

def ReturnParentTransported
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial beforeReturn : Environment (Payload s View)) : Prop :=
  let kernel := goalFunctionKernel base ro adm old
  let b : Binder := ⟨98,.returnRebind,0⟩
  match beforeReturn.replay with
  | none => ∀ returned, kernel.admitted beforeReturn b returned →
      SelectedParentTransported definition base gen ro adm old initial (beforeReturn.extend b returned)
  | some _ => ∃ returned, beforeReturn.executionValue b = some returned ∧
      kernel.admitted beforeReturn b returned ∧
      SelectedParentTransported definition base gen ro adm old initial (beforeReturn.extend b returned)

theorem selected_parent_transport
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View))
    (registered : SelectedParentRegistered definition base gen ro adm old initial beforeShared) :
    SelectedParentTransported definition base gen ro adm old initial beforeShared := by
  obtain ⟨shared,eventProof,admitted,source,parent⟩ := registered
  exact ⟨shared,eventProof,admitted,registered_parent_transport definition base gen ro adm old initial _ parent⟩

theorem return_parent_transport
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial beforeReturn : Environment (Payload s View))
    (registered : ReturnParentRegistered definition base gen ro adm old initial beforeReturn) :
    ReturnParentTransported definition base gen ro adm old initial beforeReturn := by
  cases replay : beforeReturn.replay with
  | none =>
    simp only [ReturnParentRegistered,replay] at registered
    simp only [ReturnParentTransported,replay]
    intro returned admitted
    exact selected_parent_transport definition base gen ro adm old initial _ (registered returned admitted)
  | some history =>
    simp only [ReturnParentRegistered,replay] at registered
    simp only [ReturnParentTransported,replay]
    obtain ⟨returned,lookup,admitted,parent⟩ := registered
    exact ⟨returned,lookup,admitted,selected_parent_transport definition base gen ro adm old initial _ parent⟩

/-- The actual R332 source-root alternatives now supply the missing extended
parent judgment and both children. Open invocation/return remain universal;
fixed replay keeps its actual execution lookup. -/
theorem original_source_parent_transported_alternatives
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial : Environment (Payload s View))
    (state : Decoded s View) (found : decode ro initial = some state)
    (sourceProof : SourceJudgment (goalFunctionKernel base ro adm old) initial
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root) :
    ∃ description outerView,
      Admitted base ro adm initial ⟨98,.description,0⟩ description ∧
      let afterDescription := initial.extend ⟨98,.description,0⟩ description
      Admitted base ro adm afterDescription ⟨0,.viewLogic,0⟩ outerView ∧
      let afterView := afterDescription.extend ⟨0,.viewLogic,0⟩ outerView
      ∀ call, Admitted base ro adm afterView ⟨0,.invocation,0⟩ call →
        let afterCall := afterView.extend ⟨0,.invocation,0⟩ call
        ∃ received, Admitted base ro adm afterCall ⟨98,.receipt,0⟩ received ∧
          ReturnParentTransported definition base gen ro adm old initial
            (afterCall.extend ⟨98,.receipt,0⟩ received) := by
  obtain ⟨description,outerView,hDescription,hView,calls⟩ :=
    original_source_parent_registered_alternatives definition base gen ro adm old initial state found sourceProof
  refine ⟨description,outerView,hDescription,hView,?_⟩
  dsimp only
  intro call hCall
  obtain ⟨received,hReceived,parent⟩ := calls call hCall
  exact ⟨received,hReceived,return_parent_transport definition base gen ro adm old initial _ parent⟩

end YulangClosure.OriginalSourceGoalKernelTransportR333
