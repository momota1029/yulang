import Yulang.GeneralNominalCenteredHeadStepBoundary
import Yulang.GeneralNominalCenteredPermutationSimulation

set_option backward.isDefEq.respectTransparency false

/-! Registry permutations preserve head-only applicability and post-choice
class effects at a fixed snapshot, including the extended model journal. -/
namespace Yulang.GeneralNominalCenteredHeadStepOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepEffects (State Models)
variable {roles : Roles.RoleDecls} {first last : Registry}

theorem prepared (order : Reorders first last) (pair : DeclarationReorders a b) (context) (root : Occurrence roles) :
    Prepared first context root a ↔ Prepared last context root b :=
  GeneralNominalRegistryOrder.head_ready order pair context (inputs root)

theorem head_models (pair : DeclarationReorders a b) (context) (root : Occurrence roles) (bounds model) :
    HeadModels first context root a bounds model ↔ HeadModels last context root b bounds model := by
  simp only [HeadModels,GeneralNominalRegistryOrder.private_models (first := first) (last := last) pair,
    GeneralDictionaryRecursiveOrder.report_reorders context a b pair]

theorem failed (order : Reorders first last) (pair : DeclarationReorders a b) (context) (root : Occurrence roles) :
    Failed first context root a ↔ Failed last context root b := by
  simp only [Failed,GeneralNominalRegistryOrder.metadata order context,
    GeneralNominalRegistryOrder.fresh order context.state root.identity,
    GeneralDictionaryRecursiveOrder.report_reorders context a b pair,
    head_models (first := first) (last := last) pair]

theorem survivor_forward (order : Reorders first last) (context) (root : Occurrence roles)
    (valid : Survivor first context root key children) : Survivor last context root key children := by
  obtain ⟨known,a,visible,checked,identity,role,bounds,located,ready,kids⟩ := valid
  obtain ⟨b,present,pair⟩ := reorders_visible order a visible
  let checkedOther := GeneralNominalCandidateReordering.checked_declaration order pair checked
  refine ⟨known,b,present,checkedOther,pair.id.symm.trans identity,pair.role.symm.trans role,
    bounds,located,(prepared order pair context root).mp ready,?_⟩
  rw [kids,GeneralDictionaryRecursiveOrder.report_reorders context a b pair bounds]
  exact GeneralNominalRegistryOrder.children order pair context.state (inputs root) checked checkedOther _

theorem survivor (order : Reorders first last) (context) (root : Occurrence roles) (key children) :
    Survivor first context root key children ↔ Survivor last context root key children :=
  ⟨survivor_forward order context root,survivor_forward (GeneralRegistryChildOrder.reorders_symm order) context root⟩

theorem unique (order : Reorders first last) (context) (root : Occurrence roles) (key children) :
    Unique first context root key children ↔ Unique last context root key children := by
  simp only [Unique,survivor order context root]

theorem inspection_pending_forward (order : Reorders first last) (context) (root : Occurrence roles)
    (valid : InspectionPending first context root) : InspectionPending last context root := by
  obtain ⟨known,a,visible,role,notFailed,notPrepared⟩ := valid
  obtain ⟨b,present,pair⟩ := reorders_visible order a visible
  exact ⟨known,b,present,pair.role.symm.trans role,
    fun fail => notFailed ((failed order pair context root).mpr fail),
    fun ready => notPrepared ((prepared order pair context root).mpr ready)⟩

theorem inspection_pending (order : Reorders first last) (context) (root : Occurrence roles) :
    InspectionPending first context root ↔ InspectionPending last context root :=
  ⟨inspection_pending_forward order context root,
    inspection_pending_forward (GeneralRegistryChildOrder.reorders_symm order) context root⟩

open GeneralNominalCenteredPlanReordering (rebase)
variable {plan : Plan roles} {declaration : Declaration}

theorem output_schema (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (state root) :
    outputSchema state root (rebase plan order pair) = outputSchema state root plan := by
  simp only [outputSchema,Plan.schema,rebase,GeneralNominalPacketReordering.rebase,pair.associated]

theorem effects_ready (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (state root) :
    EffectsReady state root (rebase plan order pair) ↔ EffectsReady state root plan := by
  unfold EffectsReady
  rw [output_schema]
  change (∀ output ∈ requests state root, ∃ equation ∈ declaration.associated, equation.name = output.name) ∧ _ ↔ _
  rw [pair.associated]

theorem head_equations (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (model) :
    HeadEquations (rebase plan order pair) model ↔ HeadEquations plan model := by
  have capture : GeneralNominalPacketSupport.capture (rebase plan order pair).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketReordering.capture order pair
  simp only [HeadEquations,GeneralNominalCenteredPlanReordering.head_schema,
    GeneralNominalCenteredPlanReordering.schema_holds,GeneralNominalCenteredPlanReordering.binder]
  change (plan.input.Holds model ∧ _ ∧ _) ↔ _
  rw [capture]
  change (plan.input.Holds model ∧ (∀ name ∈ declaration.inputNames, _) ∧ _) ↔ _
  simp only [Declaration.inputNames,pair.head]

theorem output_equations (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (state root model) :
    OutputEquations state root (rebase plan order pair) model ↔ OutputEquations state root plan model := by
  simp only [OutputEquations,output_schema,GeneralNominalCenteredPlanReordering.schema_holds]

theorem frame (order : Reorders first last)
    (pair : DeclarationReorders plan.packet.declaration declaration)
    (visible : declaration ∈ last.declarations)
    (given : Frame first state root key plan) :
    Frame last state root key (rebase plan (given.registry_eq ▸ order) pair) where
  registry_eq := rfl
  context_eq := given.context_eq
  occurrence_eq := given.occurrence_eq
  key_eq := pair.id.symm.trans given.key_eq
  raw_recorded := given.raw_recorded
  center_recorded := given.center_recorded
  visible := visible
  role_eq := pair.role.symm.trans given.role_eq
  located := given.located
  prepared := (prepared order pair state.erased.current.context root).mp given.prepared

theorem chosen_head_forward (order : Reorders first last) (state) (root : Occurrence roles) (key model)
    (chosen : ChosenHead first state root key model) : ChosenHead last state root key model := by
  obtain ⟨⟨children,only⟩,plan,given,ready,head⟩ := chosen
  obtain ⟨declaration,visible,pair⟩ := reorders_visible order plan.packet.declaration given.visible
  let packetOrder : Reorders plan.packet.registry last := given.registry_eq ▸ order
  exact ⟨⟨children,(unique order state.erased.current.context root key children).mp only⟩,
    rebase plan packetOrder pair,frame order pair visible given,
    (effects_ready packetOrder pair state root).mpr ready,(head_equations packetOrder pair model).mpr head⟩

theorem chosen_head (order : Reorders first last) (state) (root : Occurrence roles) (key model) :
    ChosenHead first state root key model ↔ ChosenHead last state root key model :=
  ⟨chosen_head_forward order state root key model,
    chosen_head_forward (GeneralRegistryChildOrder.reorders_symm order) state root key model⟩

theorem chosen_effects_forward (order : Reorders first last) (state) (root : Occurrence roles) (key model)
    (chosen : ChosenClassEffects first state root key model) : ChosenClassEffects last state root key model := by
  obtain ⟨⟨children,only⟩,plan,given,ready,head,outputs⟩ := chosen
  obtain ⟨declaration,visible,pair⟩ := reorders_visible order plan.packet.declaration given.visible
  let packetOrder : Reorders plan.packet.registry last := given.registry_eq ▸ order
  exact ⟨⟨children,(unique order state.erased.current.context root key children).mp only⟩,
    rebase plan packetOrder pair,frame order pair visible given,
    (effects_ready packetOrder pair state root).mpr ready,(head_equations packetOrder pair model).mpr head,
    (output_equations packetOrder pair state root model).mpr outputs⟩

theorem chosen_effects (order : Reorders first last) (state) (root : Occurrence roles) (key model) :
    ChosenClassEffects first state root key model ↔ ChosenClassEffects last state root key model :=
  ⟨chosen_effects_forward order state root key model,
    chosen_effects_forward (GeneralRegistryChildOrder.reorders_symm order) state root key model⟩

theorem conflict (order : Reorders first last) (state : State roles) (root : Occurrence roles) (key) :
    GeneralNominalCenteredHeadStepBoundary.OutputConflict first state root key ↔
      GeneralNominalCenteredHeadStepBoundary.OutputConflict last state root key := by
  simp only [GeneralNominalCenteredHeadStepBoundary.OutputConflict,chosen_head order,chosen_effects order]

theorem candidate_cycle_forward (order : Reorders first last) (state) (root : Occurrence roles)
    (cycle : GeneralNominalCenteredHeadBoundary.CandidateCycle first state root) :
    GeneralNominalCenteredHeadBoundary.CandidateCycle last state root := by
  obtain ⟨plan,recorded,input,registryEq,contextEq,visible,role,ready,located,entry,member,cyclic⟩ := cycle
  obtain ⟨other,present,pair⟩ := reorders_visible order plan.packet.declaration visible
  let packetOrder : Reorders plan.packet.registry last := registryEq ▸ order
  refine ⟨rebase plan packetOrder pair,recorded,input,rfl,contextEq,present,pair.role.symm.trans role,
    (prepared order pair plan.packet.context root).mp ready,located,entry,?_,cyclic⟩
  simpa only [GeneralNominalCenteredPlanReordering.inspection] using member

theorem candidate_cycle (order : Reorders first last) (state) (root : Occurrence roles) :
    GeneralNominalCenteredHeadBoundary.CandidateCycle first state root ↔
      GeneralNominalCenteredHeadBoundary.CandidateCycle last state root :=
  ⟨candidate_cycle_forward order state root,
    candidate_cycle_forward (GeneralRegistryChildOrder.reorders_symm order) state root⟩

theorem boundary_pending (order : Reorders first last) (state) (root : Occurrence roles) :
    GeneralNominalCenteredHeadBoundary.InspectionPending first state root ↔
      GeneralNominalCenteredHeadBoundary.InspectionPending last state root := by
  simp only [GeneralNominalCenteredHeadBoundary.InspectionPending,inspection_pending order,
    GeneralNominalCandidateReordering.recursive_candidateK2 order,
    GeneralNominalCandidateReordering.cycle_candidateK2 order,
    GeneralNominalCenteredAdministrativeOrder.decision_iff order]

theorem boundary_candidate (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    (GeneralNominalCenteredHeadStepBoundary.boundary roles).CandidateK2 first state root ↔
      (GeneralNominalCenteredHeadStepBoundary.boundary roles).CandidateK2 last state root :=
  or_congr (GeneralNominalCandidateReordering.feedback_candidateK2 order state.core.erased.current (inputs root))
    (candidate_cycle order state.core root)

theorem safe (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    B4TargetV6.SafeKnown (GeneralNominalCenteredHeadStepBoundary.boundary roles) first state root ↔
      B4TargetV6.SafeKnown (GeneralNominalCenteredHeadStepBoundary.boundary roles) last state root :=
  and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (not_congr (boundary_candidate order state root)) (not_congr (boundary_pending order state.core root))))

theorem rejection (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    B4TargetV6.RejectReason (GeneralNominalCenteredHeadStepBoundary.boundary roles) first state root ↔
      B4TargetV6.RejectReason (GeneralNominalCenteredHeadStepBoundary.boundary roles) last state root := by
  unfold B4TargetV6.RejectReason
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  apply or_congr (boundary_candidate order state root)
  apply and_congr (not_congr (boundary_pending order state.core root))
  change ((∀ key children, ¬ Survivor first _ root key children) ∨
    ∃ key children, Unique first _ root key children ∧ GeneralNominalCenteredHeadStepBoundary.OutputConflict first state root key) ↔ _
  simp only [survivor order,unique order,conflict order]
  rfl

theorem local_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles) (frontier)
    (valid : GeneralNominalCenteredHeadStepBoundary.Local first state root frontier) :
    GeneralNominalCenteredHeadStepBoundary.Local last state root frontier := by
  cases valid with
  | pending pending => exact .pending pending
  | inspectionPending known pending noRoot noCandidate =>
      exact .inspectionPending known ((boundary_pending order state.core root).mp pending) noRoot
        ((not_congr (boundary_candidate order state root)).mp noCandidate)
  | rejected reason => exact .rejected ((rejection order state root).mp reason)
  | ambiguous ready one two different =>
      exact .ambiguous ((safe order state root).mp ready)
        ((survivor order _ root _ _).mp one) ((survivor order _ root _ _).mp two) different
  | selected ready only clear =>
      exact .selected ((safe order state root).mp ready) ((unique order _ root _ _).mp only)
        ((not_congr (conflict order state root _)).mp clear)

theorem local_iff (order : Reorders first last) (state : State roles) (root : Occurrence roles) (frontier) :
    GeneralNominalCenteredHeadStepBoundary.Local first state root frontier ↔
      GeneralNominalCenteredHeadStepBoundary.Local last state root frontier :=
  ⟨local_forward order state root frontier,
    local_forward (GeneralRegistryChildOrder.reorders_symm order) state root frontier⟩

end Yulang.GeneralNominalCenteredHeadStepOrder
