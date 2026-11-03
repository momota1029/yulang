import YulangClosure.OriginalSourceAdmittedImageR333
import YulangClosure.OriginalSourcePublicationTransportR333

/-!
R333. Conservative primitive-kernel transport along the R331 environment
embedding. Admission is the actual `admissionKernel` of the extended Inputs,
readout and local admissions. Primitive fields are direct images of independent
original evidence, never definitions in terms of target source judgments.

Authority: SG §§3.1–3.3, SRC §6, and the original source environment. This
constructs a conservative instance; it does not identify that instance with
an authenticated native semantic kernel.
-/
namespace YulangClosure.OriginalSourceKernelTransportR333
open OriginalSource OriginalScopedClosure OriginalSourceEnvironment
open OriginalSourceInterpretation OriginalInterfacePreservationR328
open OriginalSourceViewRegistrationR330 OriginalSourceEnvironmentTransportR331
open OriginalSourcePrefixBridgeR332
open OriginalSourceAdmittedImageR333 OriginalSourcePublicationTransportR333

variable {s : Sorts} {View G : Type}

/-- The six primitive relations retain exactly their source evidence and
indices. The two admission fields here are irrelevant placeholders, replaced
together by the existing `admissionKernel` below. -/
noncomputable def primitiveKernel (g : G) (old : Kernel (Payload s View)) :
    Kernel (Payload (extended s G) (Sum View Unit)) where
  atom after a := ∃ before, environment g before = after ∧ old.atom before a
  admitted after b v := ∃ before original,
    environment g before = after ∧ scopedValue g original = v ∧ old.admitted before b original
  primitiveCheck after declaration goal :=
    ∃ before, environment g before = after ∧ old.primitiveCheck before declaration goal
  structuralShape after rule goal children :=
    ∃ before, environment g before = after ∧ old.structuralShape before rule goal children
  functionShape after goal domain binder observation :=
    ∃ before, environment g before = after ∧ old.functionShape before goal domain binder observation
  boundaryTag after site context lower upper mode :=
    ∃ before, environment g before = after ∧ old.boundaryTag before site context lower upper mode
  conversion after site context lower upper declaration :=
    ∃ before, environment g before = after ∧ old.conversion before site context lower upper declaration
  checkingAdmitted after goal b v := ∃ before original,
    environment g before = after ∧ scopedValue g original = v ∧ old.checkingAdmitted before goal b original

noncomputable def transportedKernel (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) : Kernel (Payload (extended s G) (Sum View Unit)) :=
  admissionKernel (inputs base gen) (readout g ro) (admissions g adm) (primitiveKernel g old)

/-- The environment image loses no source strategy, publication record,
ordered name/history entry, replay or initializer data. -/
theorem environment_injective (g : G) :
    Function.Injective (environment (s := s) (View := View) g) := by
  intro a b same
  have roots : a.root = b.root := payload_injective g (congrArg Environment.root same)
  have anchorMaps : a.anchors = b.anchors := by
    funext key
    apply scopedValue_injective g
    rw [← anchors_preserved g a key, ← anchors_preserved g b key]
    exact congrArg (fun env => env.anchors (anchorKey g key)) same
  have publicationMaps : a.publications = b.publications := by
    funext key
    apply option_injective _ (publicationRecord_injective g)
    rw [← publications_preserved g a key, ← publications_preserved g b key]
    exact congrArg (fun env => env.publications (publicationId g key)) same
  have origins : a.origin = b.origin :=
    congrArg (fun e : Environment (Payload (extended s G) (Sum View Unit)) => e.origin) same
  have paths : a.eventPath = b.eventPath :=
    list_injective _ (step_injective g) (congrArg Environment.eventPath same)
  have nameLists : a.names = b.names := names_injective g (congrArg Environment.names same)
  have frameLists : a.frames = b.frames :=
    list_injective _ (frame_injective g) (congrArg Environment.frames same)
  have replays : a.replay = b.replay :=
    option_injective _ (list_injective _ (frame_injective g)) (congrArg Environment.replay same)
  have initializerLists : a.initializers = b.initializers :=
    list_injective _ (initializer_injective g) (congrArg Environment.initializers same)
  cases a; cases b
  cases roots; cases anchorMaps; cases publicationMaps; cases origins; cases paths
  cases nameLists; cases frameLists; cases replays; cases initializerLists
  rfl

theorem primitive_image_iff (g : G) (P : Environment (Payload s View) → Prop)
    (env : Environment (Payload s View)) :
    (∃ before, environment g before = environment g env ∧ P before) ↔ P env := by
  constructor
  · rintro ⟨before,same,valid⟩
    exact environment_injective g same ▸ valid
  · intro valid
    exact ⟨env,rfl,valid⟩

/-- Conservativity is reflection as well as preservation, for each original
primitive relation independently. No old primitive is enlarged on an image. -/
theorem primitive_fields_conservative (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) :
    (∀ a, (primitiveKernel g old).atom (environment g env) a ↔ old.atom env a) ∧
    (∀ declaration goal, (primitiveKernel g old).primitiveCheck (environment g env) declaration goal ↔
      old.primitiveCheck env declaration goal) ∧
    (∀ rule goal children, (primitiveKernel g old).structuralShape (environment g env) rule goal children ↔
      old.structuralShape env rule goal children) ∧
    (∀ goal domain binder observation,
      (primitiveKernel g old).functionShape (environment g env) goal domain binder observation ↔
        old.functionShape env goal domain binder observation) ∧
    (∀ site context lower upper mode,
      (primitiveKernel g old).boundaryTag (environment g env) site context lower upper mode ↔
        old.boundaryTag env site context lower upper mode) ∧
    (∀ site context lower upper declaration,
      (primitiveKernel g old).conversion (environment g env) site context lower upper declaration ↔
        old.conversion env site context lower upper declaration) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a; exact primitive_image_iff g (fun e => old.atom e a) env
  · intro declaration goal; exact primitive_image_iff g (fun e => old.primitiveCheck e declaration goal) env
  · intro rule goal children; exact primitive_image_iff g (fun e => old.structuralShape e rule goal children) env
  · intro goal domain binder observation
    exact primitive_image_iff g (fun e => old.functionShape e goal domain binder observation) env
  · intro site context lower upper mode
    exact primitive_image_iff g (fun e => old.boundaryTag e site context lower upper mode) env
  · intro site context lower upper declaration
    exact primitive_image_iff g (fun e => old.conversion e site context lower upper declaration) env

theorem atom_transport (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (a : Atom) (valid : old.atom env a) :
    (primitiveKernel g old).atom (environment g env) a := ⟨env,rfl,valid⟩

theorem primitive_transport (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (declaration : Declaration) (goal : CheckGoal)
    (valid : old.primitiveCheck env declaration goal) :
    (primitiveKernel g old).primitiveCheck (environment g env) declaration goal := ⟨env,rfl,valid⟩

theorem structural_transport (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (rule : StructuralCheck) (goal : CheckGoal)
    (children : List CheckGoal) (valid : old.structuralShape env rule goal children) :
    (primitiveKernel g old).structuralShape (environment g env) rule goal children := ⟨env,rfl,valid⟩

theorem function_transport (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (goal domain : CheckGoal) (binder : Binder)
    (observation : CheckGoal) (valid : old.functionShape env goal domain binder observation) :
    (primitiveKernel g old).functionShape (environment g env) goal domain binder observation := ⟨env,rfl,valid⟩

theorem boundaryTag_transport (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (site : Site) (context : Context)
    (lower upper : Endpoint) (mode : CheckMode) (valid : old.boundaryTag env site context lower upper mode) :
    (primitiveKernel g old).boundaryTag (environment g env) site context lower upper mode := ⟨env,rfl,valid⟩

theorem conversion_transport (g : G) (old : Kernel (Payload s View))
    (env : Environment (Payload s View)) (site : Site) (context : Context)
    (lower upper : Endpoint) (declaration : Declaration)
    (valid : old.conversion env site context lower upper declaration) :
    (primitiveKernel g old).conversion (environment g env) site context lower upper declaration := ⟨env,rfl,valid⟩

/-- Function observations quantify over every actually admitted target
candidate. The exact image theorem supplies its original preimage. -/
theorem checking_transport (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) {env : Environment (Payload s View)} {goal : CheckGoal}
    (checked : Checking (admissionKernel base ro adm old) env goal) :
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
      (function_transport g old env goal domain binder observation shape) domainIH ?_
    intro candidate valid
    obtain ⟨original, rfl, admitted⟩ := (admitted_image_iff g base gen ro adm env binder candidate).mp valid
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
    (proof : Boundary (admissionKernel base ro adm old) env site context lower upper) :
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
    (proof : Local (admissionKernel base ro adm old) env premise) :
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
    (proof : Judgment (admissionKernel base ro adm old) env tree) :
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
    (proof : SourceJudgment (admissionKernel base ro adm old) env context source) :
    SourceJudgment (transportedKernel g base gen ro adm old) (environment g env) context source :=
  judgment_transport g base gen ro adm old proof

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
    apply (OriginalModuleContextBindingR315.original_parent_formation_iff base ro adm old reached).mpr
    exact ⟨annotations,occurrence,data,state,found,admitted,formation,locals,callee,argument⟩

theorem register_actual_parent_transport
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial reached : Environment (Payload s View))
    (initialState : Decoded s View) (initialFound : decode ro initial = some initialState)
    (priorData : Logical s View) (priorOccurrence : Nat)
    (registered : RegisteredAt definition base gen ro adm initial reached priorData priorOccurrence)
    (source : SourceJudgment (admissionKernel base ro adm old) reached selectedContext selectedSource) :
    ParentTransportedAt definition base gen ro adm old initial reached :=
  registered_parent_transport definition base gen ro adm old initial reached
    (register_actual_parent definition base gen ro adm old initial reached initialState initialFound
      priorData priorOccurrence registered source)

def SelectedParentTransported
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial beforeShared : Environment (Payload s View)) : Prop :=
  let kernel := admissionKernel base ro adm old
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
  let kernel := admissionKernel base ro adm old
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
    (sourceProof : SourceJudgment (admissionKernel base ro adm old) initial
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

end YulangClosure.OriginalSourceKernelTransportR333
