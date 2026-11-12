import Yulang.GeneralNominalMaterializedHeadRecovery
import Yulang.GeneralNominalWhereRequestMembership

/-! Actual stored root requests supply output equivalence without output paths.
Declared associated-name existence comes from the guarded installation. -/
namespace Yulang.GeneralNominalHistoricalOutputRecovery
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralNominalMaterialization GeneralDeclarations
open GeneralNominalMaterializedHeadRecovery

/-- Defined root names yield the actual first-match equation chosen by requests. -/
theorem root_find (declaration : Declaration) (root : GeneralSourceDictionaries.Occurrence roles)
    (defined : RootDefined declaration root) (output : GeneralSourceState.Output)
    (member : output ∈ root.demand.outputs) :
    ∃ equation, declaration.associated.find? (fun e => e.name == output.name) = some equation := by
  cases found : declaration.associated.find? (fun e => e.name == output.name) with
  | some equation => exact ⟨equation,rfl⟩
  | none =>
    obtain ⟨equation,present,name⟩ := defined output member
    have absent := List.find?_eq_none.mp found equation present
    simp [name] at absent

/-- The exact lookup result is an actual root materialization request. -/
theorem root_request_member (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings) (output : GeneralSourceState.Output)
    (member : output ∈ root.demand.outputs) (equation : Equation)
    (found : declaration.associated.find? (fun e => e.name == output.name) = some equation) :
    (⟨equation.rhs,output.target,.actual⟩ : Request) ∈ requests state registry root declaration checked captures := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨output,member,List.mem_map.mpr ⟨equation,?_,rfl⟩⟩
  simp [found]

/-- Recover every demanded root output from the stored branch in the current
caller's model. No equality certificate or Equivalent premise is supplied. -/
theorem root_outputs_equivalent (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.current.packets)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (recorded : packet.context.state.nominals slot = some descriptor)
    (headBounds : packet.bounds = [(slot,slot)]) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (translated : ∀ output ∈ packet.site.occurrence.demand.outputs, ∀ equation,
      packet.declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state.current model) :
    ∀ output ∈ packet.site.occurrence.demand.outputs,
      Equivalent (model output.target).1 (model (packet.context.state.base.source slot)).1 := by
  intro output present
  obtain ⟨equation,found⟩ := root_find packet.declaration packet.site.occurrence
    (GeneralNominalHistoricalSelectedEvidence.packet_root_defined registry root state formed packet member) output present
  exact packet_request_equivalent state.current packet member slot descriptor recorded headBounds names bounds parameters query
    ⟨equation.rhs,output.target,.actual⟩
    (root_request_member packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked
      packet.bindings output present equation found) rfl (translated output present equation found) model valid

/-- With no output binders, the actual child target is the allocation identity,
not any member of the captured interval; arbitrary width changes are harmless. -/
theorem output_target_allocated (declaration : Declaration)
    (noOutputBinders : declaration.outputNames = [])
    (capture : GeneralDeclarationDemands.Capture) (allocate : Nat → Nat) (equation : Equation) :
    GeneralDeclarationDemands.outputTarget declaration capture allocate equation = allocate equation.id := by
  unfold GeneralDeclarationDemands.outputTarget
  cases GeneralDeclarationPatterns.normalize equation.rhs <;> simp [noOutputBinders]

/-- Actual child output allocation identities depend on the retained seed,
invocation/declaration/equation IDs, not registry or descriptor interval syntax. -/
theorem child_target_same_seed (before after : GeneralNominalState.State)
    (first last : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (noOutputBinders : declaration.outputNames = [])
    (oldBindings newBindings : GeneralNominalAllocation.Bindings)
    (clause : Clause) (equation : Equation) (seed : before.seed = after.seed) :
    GeneralDeclarationDemands.outputTarget declaration
      (GeneralNominalAllocation.capture before first root.identity declaration.id oldBindings)
      (GeneralNominalAllocation.allocation (roles := roles) before first root.identity declaration.id clause).outputs equation =
    GeneralDeclarationDemands.outputTarget declaration
      (GeneralNominalAllocation.capture after last root.identity declaration.id newBindings)
      (GeneralNominalAllocation.allocation (roles := roles) after last root.identity declaration.id clause).outputs equation := by
  rw [output_target_allocated declaration noOutputBinders,output_target_allocated declaration noOutputBinders]
  simp only [GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,seed]

/-- Every original where output has an actual canonical request and hence its
whole-head equality is recovered from the recorded packet, even nonterminally. -/
theorem child_outputs_equivalent (state : GeneralNominalSaturationState.State roles)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.packets)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (recorded : packet.context.state.nominals slot = some descriptor)
    (headBounds : packet.bounds = [(slot,slot)]) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (translated : ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state model) :
    ∀ clause ∈ packet.declaration.requirements, ∀ equation ∈ clause.outputs,
      Equivalent (model (GeneralDeclarationDemands.outputTarget packet.declaration
        (GeneralNominalAllocation.capture packet.context.state packet.registry packet.site.occurrence.identity packet.declaration.id packet.bindings)
        (GeneralNominalAllocation.allocation (roles := roles) packet.context.state packet.registry packet.site.occurrence.identity packet.declaration.id clause).outputs equation)).1
        (model (packet.context.state.base.source slot)).1 := by
  intro clause hc equation he
  exact packet_request_equivalent state packet member slot descriptor recorded headBounds names bounds parameters query _
    (GeneralNominalWhereRequestMembership.child_request_member packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings clause hc equation he) rfl (translated clause hc equation he) model valid

end Yulang.GeneralNominalHistoricalOutputRecovery
