import Yulang.GeneralDictionaryCenteredPointCandidate179
import Yulang.GeneralDictionaryNominalPairSourceSupport178
import Yulang.GeneralDictionaryCenteredNovel177

/-! Initial singleton installation for the finite linear nominal point fragment.
No support or joint-centered-model premise is required by the final producer. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCenteredPointInstall179
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryLinearLeaf
open GeneralDictionaryNominalPairSourceSupport178

variable {roles : Roles.RoleDecls}

theorem reads_exact (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : LinearLeafShape context root declaration) :
    GeneralNominalSupport.readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation declaration)
      [(shape.slot,shape.slot)] = [shape.slot] := by
  rw [shape.query]
  simp only [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads,shape.recorded,
    shape.parameters,GeneralNominalLinearCaptureFacts.typeArguments_exact,↓reduceIte]
  rw [variables_read_none]
  rfl

theorem inspection (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : LinearLeafShape context root declaration) :
    GeneralNominalSupport.Inspection (GeneralNominalSupport.initial context root) [] declaration
      [(shape.slot,shape.slot)] := by
  intro slot member
  change slot ∈ GeneralNominalSupport.readsMany context.state
    (GeneralNominalInspection.queries context.state context.interpretation declaration) [(shape.slot,shape.slot)] at member
  rw [reads_exact context root declaration shape] at member
  cases List.mem_singleton.mp member
  exact nominal_source_ready context root shape.slot shape.descriptor shape.recorded

theorem support_guard (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : LinearLeafShape context root declaration) :
    GeneralNominalSupport.Guard (GeneralNominalSupport.initial context root) root declaration
      [(shape.slot,shape.slot)] [] := by
  refine ⟨?_,?_,inspection context root declaration shape⟩
  · intro _ member; cases member
  · intro index
    rw [located_arguments context root shape.slot shape.slot shape.located index]
    exact nominal_source_ready context root shape.slot shape.descriptor shape.recorded

theorem support_decisions (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : LinearLeafShape context root declaration) (registry : Registry)
    (singleton : registry.declarations = [declaration]) :
    GeneralNominalSupport.DecisionGuard (GeneralNominalSupport.initial context root) registry root [] := by
  refine ⟨?_,(support_guard context root declaration shape).2.1,?_⟩
  · intro _ member; cases member
  · intro other member role intervals found
    rw [singleton] at member
    cases List.mem_singleton.mp member
    have same := Option.some.inj (shape.located.symm.trans found)
    subst intervals
    exact inspection context root declaration shape

variable {registry : Registry} {context : Context} {input : Site roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem raw_installable
    (candidate : Candidate registry (initialAt context input) focus key children plan)
    (selected : GeneralNominalCenteredBoundary.Local registry (initialAt context input) focus (.selected key children)) :
    GeneralNominalFeedbackSteps.Installable registry (initialAt context input).erased.current plan.packet := by
  have siteEq : plan.packet.site = GeneralNominalDemandMerging.pointSite input.occurrence :=
    List.mem_singleton.mp candidate.raw_recorded
  have contextEq : plan.packet.context = context := candidate.context_eq
  have occurrenceEq : plan.packet.site.occurrence = input.occurrence := congrArg (fun s => s.occurrence) siteEq
  have old : GeneralNominalFeedbackK2.Local registry (initialAt context input).erased.current
      plan.packet.site.occurrence (.selected plan.packet.declaration.id plan.packet.children) := by
    rw [candidate.occurrence_eq,candidate.key_eq,candidate.children_eq]
    cases selected with
    | selected safe unique =>
      exact .selected ⟨safe.1,fun h => safe.2.1 (.inl h),fun h => safe.2.2.1 (.inl h),
        fun h => safe.2.2.2 (.inl h)⟩ unique
  obtain ⟨model,branch⟩ := candidate.branch
  have role : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role := by
    rw [candidate.occurrence_eq]; exact candidate.role
  have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
    rw [candidate.registry_eq]; exact candidate.visible
  have joint := GeneralNominalJointCandidates.initial_joint plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration visible plan.packet.checked role
    plan.packet.bounds candidate.located candidate.prepared model branch
  refine ⟨?_,old,?_⟩
  · refine ⟨candidate.registry_eq,candidate.context_eq,candidate.raw_recorded,candidate.visible,?_,
      candidate.located,candidate.prepared,GeneralNominalFeedbackK2.selected_legacy old,?_,?_,?_,?_⟩
    · rw [candidate.occurrence_eq]; exact candidate.role
    · intro prior member; cases member
    · intro other member _
      have same : other = GeneralNominalDemandMerging.pointSite input.occurrence := List.mem_singleton.mp member
      rw [siteEq,same]; exact .refl _
    · have source := (branch_interval_sound plan.packet.registry plan.packet.context plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked plan.packet.bounds model branch).1
      rw [contextEq] at source
      exact ⟨model,(GeneralNominalSaturationState.initial_models ..).mpr source,branch⟩
    · simpa only [candidate.registry_eq,contextEq,occurrenceEq,initialAt,GeneralNominalSupport.initial] using joint
  · intro other member _
    have same : other = GeneralNominalDemandMerging.pointSite input.occurrence := List.mem_singleton.mp member
    rw [siteEq,same]; exact .refl _


 theorem value_guard
    (candidate : Candidate registry (initialAt context input) focus key children plan)
    (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)
    (singleton : registry.declarations = [plan.packet.declaration]) :
    GeneralNominalValueSupport.PacketGuard (initialAt context input).erased plan.packet [] := by
  have siteEq : plan.packet.site = GeneralNominalDemandMerging.pointSite input.occurrence :=
    List.mem_singleton.mp candidate.raw_recorded
  have contextEq : plan.packet.context = context := candidate.context_eq
  subst context
  have occurrenceEq : plan.packet.site.occurrence = input.occurrence := congrArg (fun s => s.occurrence) siteEq
  have packetLocated : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  have one := support_guard plan.packet.context plan.packet.site.occurrence plan.packet.declaration shape
  have two := support_decisions plan.packet.context plan.packet.site.occurrence plan.packet.declaration
    shape plan.packet.registry (by rw [candidate.registry_eq]; exact singleton)
  apply GeneralNominalValueSupport.source_packet
  constructor
  · rw [← packetLocated] at one
    simp only [GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] at one
    rw [occurrenceEq] at one
    simpa only [occurrenceEq,initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] using one
  · simpa only [occurrenceEq,initialAt,GeneralNominalSupport.initial,
      GeneralNominalSaturationState.initial] using two

 theorem installable
    (candidate : Candidate registry (initialAt context input) focus key children plan)
    (selected : GeneralNominalCenteredBoundary.Local registry (initialAt context input) focus (.selected key children))
    (singleton : registry.declarations = [plan.packet.declaration])
    (named : input.PointNames)
    (below : ∀ name ∈ GeneralNominalState.sources context.state, name ≤ context.state.seed)
    (slot : Fin plan.packet.context.state.base.slots) (name : Nat)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = []) :
    GeneralNominalCenteredBoundary.Installable registry (initialAt context input) plan := by
  obtain ⟨shape⟩ := GeneralDictionaryCenteredPointCandidate179.discovered_shape candidate slot name names
    distinct inputs query located terminal outputs
  obtain ⟨previous,branch⟩ := candidate.branch
  have source := (branch_interval_sound plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked plan.packet.bounds previous branch).1
  have contextEq : plan.packet.context = context := candidate.context_eq
  rw [contextEq] at source
  obtain ⟨extended,models,holds,_⟩ := GeneralDictionaryCenteredPointCandidate179.initial_joint candidate named below
    slot name names distinct inputs query located terminal outputs previous source
  exact ⟨raw_installable candidate selected,[],
    (GeneralDictionaryCenteredGuard177.candidate_guard_iff candidate selected []).mpr
      ⟨value_guard candidate shape singleton,extended,models,holds⟩⟩


/-- Actual initial source wrapper: pointness localizes the successful query;
source formation supplies freshness and rootSite supplies its center names. -/
 theorem initial_source_installable
    {root : Occurrence roles}
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (candidate : Candidate registry (initial context root) root key children plan)
    (selected : GeneralNominalCenteredBoundary.Local registry (initial context root) root (.selected key children))
    (singleton : registry.declarations = [plan.packet.declaration])
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : root.demand.outputs = []) :
    GeneralNominalCenteredBoundary.Installable registry (initial context root) plan := by
  obtain ⟨lower,upper,bounds⟩ := GeneralDictionaryCenteredNullary178.candidate_singleton_bounds candidate _ query
  have located := candidate.located
  rw [bounds] at located
  have same := GeneralDictionaryCenteredRootNominal178.located_point plan.packet.context
    plan.packet.site.occurrence (by rw [candidate.occurrence_eq]; exact point) lower upper located
  subst upper
  apply installable candidate selected singleton _ source.below_seed lower name names distinct inputs query
    located terminal (by rw [candidate.occurrence_eq]; exact outputs)
  intro index equal
  exact point_center context.state.seed root index equal

 theorem initial_source_stable_instance
    {root : Occurrence roles}
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (candidate : Candidate registry (initial context root) root key children plan)
    (selected : GeneralNominalCenteredBoundary.Local registry (initial context root) root (.selected key children))
    (singleton : registry.declarations = [plan.packet.declaration])
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (terminal : plan.packet.declaration.requirements = []) (outputs : root.demand.outputs = [])
    (stable : Stable registry (initial context root) root)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models (initial context root) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry context model root key children := by
  exact GeneralDictionaryCenteredNovel177.committed_or_installable_instance candidate stable
    (.inr (initial_source_installable source point candidate selected singleton name names distinct inputs query
      terminal outputs)) model valid

/-- Diagnostic implication only: a raw branch countermodel cannot coexist with
stability and enabled installation. In the linear point fragment raw branch
validity is already universal, so this does not manufacture a counterexample. -/
 theorem initial_source_bad_model_not_selected
    {root : Occurrence roles}
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (candidate : Candidate registry (initial context root) root key children plan)
    (singleton : registry.declarations = [plan.packet.declaration])
    (name : Nat) (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (terminal : plan.packet.declaration.requirements = []) (outputs : root.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models (initial context root) model)
    (bad : ¬ plan.packet.Holds model) (stable : Stable registry (initial context root) root) :
    ¬ GeneralNominalCenteredBoundary.Local registry (initial context root) root (.selected key children) := by
  intro selected
  have enabled := initial_source_installable source point candidate selected singleton name names distinct
    inputs query terminal outputs
  have committed := GeneralDictionaryCenteredReady176.stable_committed stable plan candidate.occurrence_eq enabled
  exact bad (committed.1 model valid.1)


/-- Committed is semantic, not packet-list membership. This terminal initial
point fragment is already raw-committed, so enabled installation is not a
proof of a novel transition or of failure of stability. -/
 theorem initial_committed
    (candidate : Candidate registry (initialAt context input) focus key children plan)
    (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration) :
    GeneralNominalFeedbackSteps.Committed (initialAt context input).erased.current plan.packet := by
  have located : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  constructor
  · intro model valid
    have source : GeneralNominalState.Models plan.packet.context.state model := by
      rw [candidate.context_eq]
      exact valid.1
    unfold GeneralNominalSaturationState.Packet.Holds
    rw [located]
    exact branch_models _ _ _ _ _ shape model source
  · intro child member
    rw [candidate.children_eq,
      GeneralDictionaryCenteredScalarDiscovery177.discovered_children_empty candidate shape.terminal] at member
    cases member

end Yulang.GeneralDictionaryCenteredPointInstall179
