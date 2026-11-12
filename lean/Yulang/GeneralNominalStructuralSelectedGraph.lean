import Yulang.GeneralNominalQueryRecoveredNodeEvidence

/-! Same-model current Instance needs no child evidence. A restricted singleton
journal/local-alias class then yields Joint and actual historical child edges. -/
namespace Yulang.GeneralNominalStructuralSelectedGraph
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalSharedJournalPaths
open GeneralDictionaryRecursiveEvidence GeneralNominalHistoricalSelectedEvidence
open GeneralNominalQueryRecoveredNodeEvidence

theorem selected_instance (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (slot : Fin state.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.current.context.state.base.slots)
    (recorded : state.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds state.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerPaths : ∀ i, RecordedPath state.current.context.state
      (packet.context.state.base.source (oldBounds i).1)
      (state.current.context.state.base.source (bounds i).1))
    (upperPaths : ∀ i, RecordedPath state.current.context.state
      (packet.context.state.base.source (oldBounds i).2)
      (state.current.context.state.base.source (bounds i).2))
    (headPath : RecordedPath state.current.context.state
      (packet.context.state.base.source oldSlot) (state.current.context.state.base.source slot))
    (noOutputBinders : packet.declaration.outputNames = [])
    (variables : ∀ clause ∈ packet.declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (located : arguments state.current.context packet.site.occurrence = some [(slot,slot)])
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state packet.site.occurrence (.selected key children))
 :
    packet.declaration.id = key ∧
      Instance registry state.current.context model packet.site.occurrence key children := by
  have name := packet_head_name state.current packet member oldSlot oldDescriptor oldRecorded
    slot descriptor recorded headPath model valid
  have oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])] := by
    rw [GeneralDictionarySupportMetadataInvariants.packet_queries registry root state formed packet member,query,name]
  have oldTranslated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i]) := by
    intro output ho equation found
    rw [GeneralDictionarySupportMetadataInvariants.packet_translate registry root state formed packet member,
      translated output ho equation found,name]
  have oldChildTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i]) := by
    intro clause hc equation he
    rw [GeneralDictionarySupportMetadataInvariants.packet_translate registry root state formed packet member,
      childTranslated clause hc equation he,name]
  let checked : DeclarationChecked registry.constructors roles packet.declaration := by
    have reg := GeneralDictionarySupportJournal.packet_registry registry root state formed packet member
    rw [← reg]
    exact packet.checked
  have seed := GeneralDictionarySupportSourceInvariants.packet_seed registry root state formed packet member
  have headEqual := headPath.sound model valid.1
  have roots := GeneralNominalHistoricalOutputRecovery.root_outputs_equivalent registry root state formed packet member
    oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery oldTranslated model valid
  have childOld := GeneralNominalHistoricalOutputRecovery.child_outputs_equivalent state.current packet member
    oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery oldChildTranslated model valid
  have childCurrent (clause : Clause) (hc : clause ∈ packet.declaration.requirements)
      (equation : Equation) (he : equation ∈ clause.outputs) := childOld clause hc equation he
  have childTargets : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      CommonNominalFullCarrier.Equivalent (model (GeneralDeclarationDemands.outputTarget packet.declaration
        (GeneralNominalAllocation.capture state.current.context.state registry packet.site.occurrence.identity packet.declaration.id
          (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)])))
        (GeneralNominalAllocation.allocation (roles := roles) state.current.context.state registry
          packet.site.occurrence.identity packet.declaration.id clause).outputs equation)).1
      (model (state.current.context.state.base.source slot)).1 := by
    intro clause hc equation he
    have eq := childCurrent clause hc equation he
    rw [GeneralNominalHistoricalOutputRecovery.child_target_same_seed packet.context.state state.current.context.state
      packet.registry registry packet.site.occurrence packet.declaration noOutputBinders packet.bindings
      (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)])) clause equation seed] at eq
    exact ⟨CommonNominalFullCarrier.subtype_trans eq.1 headEqual.1,
      CommonNominalFullCarrier.subtype_trans headEqual.2 eq.2⟩
  have coherent := GeneralNominalSharedJournalFacts.coherent_after_steps registry root state state .refl
    packet member oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery model valid
  rw [name] at coherent
  have currentCoherent := coherent_of_equivalent model _ _ _ names (headPath.sound model valid.1) coherent
  have merges := merges_after_steps_of_journal_paths registry root state state .refl packet member
    oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery
    slot descriptor recorded bounds parameters query lowerPaths upperPaths seed model valid
  have branch := (GeneralNominalWhereAssociatedFacts.branch_models_iff state.current.context registry
    packet.site.occurrence packet.declaration checked noOutputBinders variables slot descriptor recorded
    names declared bounds parameters query translated childTranslated model
    (fun output member => ⟨CommonNominalFullCarrier.subtype_trans (roots output member).1 headEqual.1,
      CommonNominalFullCarrier.subtype_trans headEqual.2 (roots output member).2⟩) childTargets).mpr
      ⟨valid.1,currentCoherent,merges⟩
  have finished := report_finished state.current.context packet.declaration slot descriptor recorded names bounds parameters query
  have ready := (GeneralNominalWhereAssociatedFacts.request_ready_iff state.current.context registry
    packet.site.occurrence packet.declaration checked variables [(slot,slot)] descriptor.declaration.name names
    translated childTranslated).mpr (packet_root_defined registry root state formed packet member)
  let emitted := GeneralNominalAllocation.children state.current.context.state registry packet.site.occurrence
    packet.declaration checked (bindings state.current.context.state (report state.current.context packet.declaration [(slot,slot)]))
  cases selected with
  | selected safe unique =>
    have metadata : Metadata registry state.current.context := by
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
    have inst : Instance registry state.current.context model packet.site.occurrence packet.declaration.id emitted :=
      ⟨packet.declaration,GeneralDictionarySupportJournal.packet_visible registry root state formed packet member,
        checked,rfl,packet_role registry root state formed packet member,[(slot,slot)],located,finished,ready,
        rfl,metadata,branch⟩
    have identities := unique.2 _ _ (GeneralDictionaryOrdinarySelectedReplay.survivor_of_instance registry
      state.current.context packet.site.occurrence key children unique.1 model packet.declaration.id emitted inst)
    have result : Instance registry state.current.context model packet.site.occurrence key children :=
      identities.1 ▸ identities.2 ▸ inst
    exact ⟨identities.1,result⟩

/-- The current survivor supplies common readiness; Instance supplies its own
actual same-model branch. No conversion of existential branch models is used. -/
theorem branchAt_of_instance (registry : Registry) (state : GeneralNominalSaturationState.State roles)
    (focus : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles))
    (selected : Survivor registry state.context focus key children)
    (model : GeneralNominalCommonBridge.Assignment)
    (instanceRule : Instance registry state.context model focus key children) :
    GeneralNominalJointCandidates.BranchAt registry state focus key model := by
  obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := selected
  obtain ⟨decl,visible,checked,identity,role,bounds,located,finished,ready,kids,metadata,branch⟩ := instanceRule
  exact ⟨decl,visible,checked,identity,role,
    ⟨metadata,prepared.2.1,prepared.2.2.1,bounds,located,finished,ready,model,branch⟩,
    bounds,located,branch⟩

/-- Exact one-packet and same-occurrence alias coverage replace the universal
Joint obligations for this restricted class. The one current model is retained. -/
theorem singleton_joint (registry : Registry) (state : GeneralNominalSupport.Tracked roles)
    (packet : GeneralNominalSaturationState.Packet roles) (singleton : state.current.packets = [packet])
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (identity : packet.declaration.id = key)
    (selected : GeneralNominalSupportBoundary.Local registry state packet.site.occurrence (.selected key children))
    (locality : ∀ site, GeneralNominalJointCandidates.Related state.current packet.site.occurrence site →
      site.occurrence = packet.site.occurrence)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (instanceRule : Instance registry state.current.context model packet.site.occurrence key children) :
    GeneralNominalJointCandidates.Joint registry state.current packet.site.occurrence key := by
  have survivor : Survivor registry state.current.context packet.site.occurrence key children := by
    cases selected with | selected _ unique => exact unique.1
  have branch := branchAt_of_instance registry state.current packet.site.occurrence key children survivor model instanceRule
  refine ⟨?_,model,valid,branch,?_⟩
  · intro other member alias
    rw [singleton] at member
    have same := List.mem_singleton.mp member
    subst other
    exact identity
  · intro site related
    rw [locality site related]
    exact branch

/-- Actual graph edges follow from reachable support stability and the derived
Joint, not from Evidence or a postulated generated child list. -/
theorem singleton_generated (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (singleton : state.current.packets = [packet])
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (identity : packet.declaration.id = key)
    (stable : GeneralNominalSupportSteps.Stable registry state packet.site.occurrence)
    (selected : GeneralNominalSupportBoundary.Local registry state packet.site.occurrence (.selected key children))
    (locality : ∀ site, GeneralNominalJointCandidates.Related state.current packet.site.occurrence site →
      site.occurrence = packet.site.occurrence)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (instanceRule : Instance registry state.current.context model packet.site.occurrence key children) :
    ∀ child ∈ children, GeneralNominalSaturationState.Generated state.current root child := by
  have joint := singleton_joint registry state packet singleton key children identity selected locality model valid instanceRule
  have edges := (GeneralDictionarySupportEvidence.reachable_joint_instance registry state root packet.site.occurrence
    reachable key children stable selected joint).2
  have focus := GeneralDictionaryInstallationOrigin.packet_generated registry root state
    (GeneralNominalSupportBoundary.reachable_formed registry state root reachable) packet (by rw [singleton]; simp)
  exact fun child member => GeneralNominalSaturationState.generated_trans focus (edges child member)

theorem structural_generated (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (singleton : state.current.packets = [packet])
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (slot : Fin state.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.current.context.state.base.slots)
    (recorded : state.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds state.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerPaths : ∀ i, RecordedPath state.current.context.state
      (packet.context.state.base.source (oldBounds i).1)
      (state.current.context.state.base.source (bounds i).1))
    (upperPaths : ∀ i, RecordedPath state.current.context.state
      (packet.context.state.base.source (oldBounds i).2)
      (state.current.context.state.base.source (bounds i).2))
    (headPath : RecordedPath state.current.context.state
      (packet.context.state.base.source oldSlot) (state.current.context.state.base.source slot))
    (noOutputBinders : packet.declaration.outputNames = [])
    (variables : ∀ clause ∈ packet.declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model)
    (located : arguments state.current.context packet.site.occurrence = some [(slot,slot)])
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state packet.site.occurrence (.selected key children))

    (stable : GeneralNominalSupportSteps.Stable registry state packet.site.occurrence)
    (locality : ∀ site, GeneralNominalJointCandidates.Related state.current packet.site.occurrence site →
      site.occurrence = packet.site.occurrence) :
    ∀ child ∈ children, GeneralNominalSaturationState.Generated state.current root child := by
  have formed := GeneralNominalSupportBoundary.reachable_formed registry state root reachable
  have member : packet ∈ state.current.packets := by rw [singleton]; simp
  have instanceRule := selected_instance registry root state formed packet member
    oldSlot oldDescriptor oldRecorded headBounds names declared oldBounds oldParameters
    slot descriptor recorded bounds parameters query lowerPaths upperPaths headPath noOutputBinders variables
    translated childTranslated model valid located key children selected
  exact singleton_generated registry root state reachable packet singleton key children instanceRule.1
    stable selected locality model valid instanceRule.2
end Yulang.GeneralNominalStructuralSelectedGraph
