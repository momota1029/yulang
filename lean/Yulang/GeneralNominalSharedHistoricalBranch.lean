import Yulang.GeneralNominalMergeCongruence
import Yulang.GeneralNominalSharedMaterializationFacts
import Yulang.GeneralNominalSharedJournalFacts

/-! Same-assignment branches for arbitrary finite binder sharing in actual
covered point-to-point histories. All semantic residuals are derived; structural
coverage and point hypotheses are explicit. This is not unrestricted V5. -/
namespace Yulang.GeneralNominalSharedHistoricalBranch
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalMergeCongruence
open GeneralNominalAllocation

theorem merges_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (oldPoint : ∀ i, (oldBounds i).1 = (oldBounds i).2)
    (point : ∀ i, (bounds i).1 = (bounds i).2)
    (source : packet.context.state.base.source oldSlot = after.current.context.state.base.source slot)
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after.current.context.state registry packet.site.occurrence.identity packet.declaration
        (bindings after.current.context.state (report after.current.context packet.declaration [(slot,slot)]))) := by
  have prior := GeneralNominalSupportSteps.steps_models path model valid
  have branch := prior.2.1 packet member
  change BranchModels packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds model at branch
  rw [headBounds] at branch
  have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
  have parts := (propagate_models ..).mp propagated
  have endpoints (i : Fin n) := GeneralNominalRepeatedMergeTransport.point_bounds_equivalent
    packet.context.state after.current.context.state model parts.1 valid.1
    oldSlot slot oldDescriptor descriptor oldRecorded recorded i.val (oldBounds i) (bounds i)
    (by rw [oldParameters]; simp [i.isLt]) (by rw [parameters]; simp [i.isLt])
    (oldPoint i) (point i) source name
  have oldMerge := parts.2.2
  rw [report_exact packet.context packet.declaration oldSlot oldDescriptor oldRecorded names oldBounds oldParameters oldQuery] at oldMerge
  rw [report_exact after.current.context packet.declaration slot descriptor recorded names bounds parameters query]
  simp only [bindings,captured,variablesReport,List.map_ofFn,Function.comp_def] at oldMerge ⊢
  apply (ofFn_merges_iff packet.context.state after.current.context.state packet.registry registry
    packet.site.occurrence.identity packet.declaration seed model names _ _ ?_).mp oldMerge
  intro i
  exact ⟨endpoints i,by simpa only [← oldPoint i,← point i] using endpoints i⟩

/-- Any finite name map, including repeated names and zero arguments. Actual
history supplies the coherence and current merge equations. The same-head
terminal associated output is materialized in the caller's unchanged model. -/
theorem branch_after_steps (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (oldPoint : ∀ i, (oldBounds i).1 = (oldBounds i).2)
    (point : ∀ i, (bounds i).1 = (bounds i).2)
    (source : packet.context.state.base.source oldSlot = after.current.context.state.base.source slot)
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (checked : DeclarationChecked registry.constructors roles packet.declaration)
    (terminal : packet.declaration.requirements = []) (equation : Equation)
    (associated : packet.declaration.associated = [equation])
    (output : packet.site.occurrence.demand.outputs = [⟨equation.name,after.current.context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate after.current.context.state.constructors after.current.context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    BranchModels registry after.current.context packet.site.occurrence packet.declaration checked [(slot,slot)] model := by
  apply (GeneralNominalSharedMaterializationFacts.branch_models_iff after.current.context registry
    packet.site.occurrence packet.declaration checked terminal equation associated slot descriptor recorded
    names declared bounds parameters query output translated model).mpr
  refine ⟨valid.1,?_,?_⟩
  · have same := GeneralNominalSharedJournalFacts.coherent_after_steps registry root before after path packet member
      oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery model valid
    simpa only [source,name] using same
  · exact merges_after_steps registry root before after path packet member oldSlot oldDescriptor oldRecorded headBounds
      names oldBounds oldParameters oldQuery slot descriptor recorded bounds parameters query oldPoint point source name seed model valid
/-- Source-ID preserving histories need no point-valued descriptor restriction.
Carrier slots and interval syntax may differ while endpoint identities agree. -/
theorem merges_after_steps_of_source_ids (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerSources : ∀ i, packet.context.state.base.source (oldBounds i).1 =
      after.current.context.state.base.source (bounds i).1)
    (upperSources : ∀ i, packet.context.state.base.source (oldBounds i).2 =
      after.current.context.state.base.source (bounds i).2)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after.current.context.state registry packet.site.occurrence.identity packet.declaration
        (bindings after.current.context.state (report after.current.context packet.declaration [(slot,slot)]))) := by
  have prior := GeneralNominalSupportSteps.steps_models path model valid
  have branch := prior.2.1 packet member
  change BranchModels packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds model at branch
  rw [headBounds] at branch
  have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
  have parts := (propagate_models ..).mp propagated
  have oldMerge := parts.2.2
  rw [report_exact packet.context packet.declaration oldSlot oldDescriptor oldRecorded names oldBounds oldParameters oldQuery] at oldMerge
  rw [report_exact after.current.context packet.declaration slot descriptor recorded names bounds parameters query]
  simp only [bindings,captured,variablesReport,List.map_ofFn,Function.comp_def] at oldMerge ⊢
  apply (ofFn_merges_iff packet.context.state after.current.context.state packet.registry registry
    packet.site.occurrence.identity packet.declaration seed model names _ _ ?_).mp oldMerge
  intro i
  constructor
  · rw [lowerSources i]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · rw [upperSources i]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

/-- Full same-model branch for source-ID preserving covered histories with
arbitrary interval widths. No observed coherence or merge premise is supplied. -/
theorem branch_after_steps_of_source_ids (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ before.current.packets)
    (oldSlot : Fin packet.context.state.base.slots)
    (oldDescriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (oldRecorded : packet.context.state.nominals oldSlot = some oldDescriptor)
    (headBounds : packet.bounds = [(oldSlot,oldSlot)]) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ packet.declaration.inputNames)
    (oldBounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (oldParameters : oldDescriptor.arguments = List.ofFn fun i => .type (oldBounds i))
    (oldQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal oldDescriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (slot : Fin after.current.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor after.current.context.state.base.slots)
    (recorded : after.current.context.state.nominals slot = some descriptor)
    (bounds : Fin n → GeneralNominalInspection.Bounds after.current.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries after.current.context.state after.current.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (lowerSources : ∀ i, packet.context.state.base.source (oldBounds i).1 =
      after.current.context.state.base.source (bounds i).1)
    (upperSources : ∀ i, packet.context.state.base.source (oldBounds i).2 =
      after.current.context.state.base.source (bounds i).2)
    (source : packet.context.state.base.source oldSlot = after.current.context.state.base.source slot)
    (name : oldDescriptor.declaration.name = descriptor.declaration.name)
    (seed : packet.context.state.seed = after.current.context.state.seed)
    (checked : DeclarationChecked registry.constructors roles packet.declaration)
    (terminal : packet.declaration.requirements = []) (equation : Equation)
    (associated : packet.declaration.associated = [equation])
    (output : packet.site.occurrence.demand.outputs = [⟨equation.name,after.current.context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate after.current.context.state.constructors after.current.context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    BranchModels registry after.current.context packet.site.occurrence packet.declaration checked [(slot,slot)] model := by
  apply (GeneralNominalSharedMaterializationFacts.branch_models_iff after.current.context registry
    packet.site.occurrence packet.declaration checked terminal equation associated slot descriptor recorded
    names declared bounds parameters query output translated model).mpr
  refine ⟨valid.1,?_,?_⟩
  · have same := GeneralNominalSharedJournalFacts.coherent_after_steps registry root before after path packet member
      oldSlot oldDescriptor oldRecorded headBounds names oldBounds oldParameters oldQuery model valid
    simpa only [source,name] using same
  · exact merges_after_steps_of_source_ids registry root before after path packet member oldSlot oldDescriptor oldRecorded headBounds
      names oldBounds oldParameters oldQuery slot descriptor recorded bounds parameters query lowerSources upperSources seed model valid
end Yulang.GeneralNominalSharedHistoricalBranch
