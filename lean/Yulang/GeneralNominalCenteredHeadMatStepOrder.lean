import Yulang.GeneralNominalCenteredHeadMatStepExecutor

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatStepOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepBoundary (boundary Local)
open GeneralNominalCenteredPlanReordering (rebase)
open GeneralNominalCenteredHeadMatEffects
variable {roles : Roles.RoleDecls} {first last : Registry} {plan : Plan roles} {declaration : Declaration}

theorem lookup (pair : DeclarationReorders a b) (name) :
    GeneralDictionaryAssociatedProvenance.lookup roles a name =
      GeneralDictionaryAssociatedProvenance.lookup roles b name := by
  simp only [GeneralDictionaryAssociatedProvenance.lookup,pair.associated,pair.role]

theorem compile_body (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (body) :
    compileBody (rebase plan order pair) body = compileBody plan body := by
  cases body <;> simp only [compileBody,rebase,GeneralNominalPacketReordering.rebase,order.1]

theorem body_schema (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (target body) :
    bodySchema (rebase plan order pair) target body = bodySchema plan target body := by
  simp only [bodySchema,compile_body]

theorem body_variables (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (model body) :
    bodyVariables (rebase plan order pair) model body = bodyVariables plan model body := by
  cases body with
  | explicit equation =>
      funext mode name
      have capture : GeneralNominalPacketSupport.capture (rebase plan order pair).packet =
          GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketReordering.capture order pair
      simp only [bodyVariables,variables,GeneralNominalCenteredPlanReordering.binder,capture]
      change (if name ∈ declaration.outputNames then _ else _) = _
      simp only [Declaration.outputNames,pair.outputBinders]
  | default => rfl

theorem ready (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (state root) :
    Ready state root (rebase plan order pair) ↔ Ready state root plan := by
  simp only [Ready,body_schema]
  change (∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
    ∃ body, GeneralDictionaryAssociatedProvenance.lookup roles declaration output.name = _ ∧ _) ↔ _
  simp only [lookup pair]

theorem class_effects (order : Reorders plan.packet.registry last)
    (pair : DeclarationReorders plan.packet.declaration declaration) (state root model) :
    ClassEffects state root (rebase plan order pair) model ↔ ClassEffects state root plan model := by
  simp only [ClassEffects,BodyHolds,body_schema,body_variables]
  change ((∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
    ∀ body, GeneralDictionaryAssociatedProvenance.lookup roles declaration output.name = _ → _) ∧ _) ↔ _
  simp only [lookup pair]

theorem chosen_head_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles) (key model)
    (chosen : GeneralNominalCenteredHeadMatStepLocal.ChosenHead first state root key model) :
    GeneralNominalCenteredHeadMatStepLocal.ChosenHead last state root key model := by
  obtain ⟨⟨children,only⟩,plan,frame,complete,head⟩ := chosen
  obtain ⟨declaration,visible,pair⟩ := reorders_visible order plan.packet.declaration frame.visible
  let packetOrder : Reorders plan.packet.registry last := frame.registry_eq ▸ order
  exact ⟨⟨children,(GeneralNominalCenteredHeadStepOrder.unique order _ root key children).mp only⟩,
    rebase plan packetOrder pair,GeneralNominalCenteredHeadStepOrder.frame order pair visible frame,
    (ready packetOrder pair state.core root).mpr complete,
    (GeneralNominalCenteredHeadStepOrder.head_equations packetOrder pair model).mpr head⟩

theorem chosen_head (order : Reorders first last) (state : State roles) (root : Occurrence roles) (key model) :
    GeneralNominalCenteredHeadMatStepLocal.ChosenHead first state root key model ↔
      GeneralNominalCenteredHeadMatStepLocal.ChosenHead last state root key model :=
  ⟨chosen_head_forward order state root key model,
    chosen_head_forward (GeneralRegistryChildOrder.reorders_symm order) state root key model⟩

theorem chosen_effects_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles) (key model)
    (chosen : GeneralNominalCenteredHeadMatStepLocal.ChosenEffects first state root key model) :
    GeneralNominalCenteredHeadMatStepLocal.ChosenEffects last state root key model := by
  obtain ⟨⟨children,only⟩,plan,frame,complete,head,effects⟩ := chosen
  obtain ⟨declaration,visible,pair⟩ := reorders_visible order plan.packet.declaration frame.visible
  let packetOrder : Reorders plan.packet.registry last := frame.registry_eq ▸ order
  exact ⟨⟨children,(GeneralNominalCenteredHeadStepOrder.unique order _ root key children).mp only⟩,
    rebase plan packetOrder pair,GeneralNominalCenteredHeadStepOrder.frame order pair visible frame,
    (ready packetOrder pair state.core root).mpr complete,
    (GeneralNominalCenteredHeadStepOrder.head_equations packetOrder pair model).mpr head,
    (class_effects packetOrder pair state.core root model).mpr effects⟩

theorem chosen_effects (order : Reorders first last) (state : State roles) (root : Occurrence roles) (key model) :
    GeneralNominalCenteredHeadMatStepLocal.ChosenEffects first state root key model ↔
      GeneralNominalCenteredHeadMatStepLocal.ChosenEffects last state root key model :=
  ⟨chosen_effects_forward order state root key model,
    chosen_effects_forward (GeneralRegistryChildOrder.reorders_symm order) state root key model⟩

theorem conflict (order : Reorders first last) (state : State roles) (root : Occurrence roles) (key) :
    GeneralNominalCenteredHeadMatStepLocal.OutputConflict first state root key ↔
      GeneralNominalCenteredHeadMatStepLocal.OutputConflict last state root key := by
  simp only [GeneralNominalCenteredHeadMatStepLocal.OutputConflict,chosen_head order,chosen_effects order]

theorem candidate_cycle_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles)
    (cycle : GeneralNominalCenteredHeadMatStepCycles.CandidateCycle first state root) :
    GeneralNominalCenteredHeadMatStepCycles.CandidateCycle last state root := by
  obtain ⟨plan,frame,entry,member,cyclic⟩ := cycle
  obtain ⟨declaration,visible,pair⟩ := reorders_visible order plan.packet.declaration frame.visible
  let packetOrder : Reorders plan.packet.registry last := frame.registry_eq ▸ order
  refine ⟨rebase plan packetOrder pair,?_,entry,?_,cyclic⟩
  · exact pair.id ▸ GeneralNominalCenteredHeadStepOrder.frame order pair visible frame
  · simpa only [GeneralNominalCenteredPlanReordering.inspection] using member

theorem candidate (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    (boundary roles).CandidateK2 first state root ↔ (boundary roles).CandidateK2 last state root :=
  or_congr (GeneralNominalCandidateReordering.cycle_candidateK2 order _ _)
    ⟨candidate_cycle_forward order state root,
      candidate_cycle_forward (GeneralRegistryChildOrder.reorders_symm order) state root⟩

theorem pending (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    (boundary roles).InspectionPending first state root ↔ (boundary roles).InspectionPending last state root :=
  or_congr (GeneralNominalCenteredHeadStepOrder.inspection_pending order _ root) Iff.rfl

theorem safe (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    B4TargetV6.SafeKnown (boundary roles) first state root ↔ B4TargetV6.SafeKnown (boundary roles) last state root :=
  and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (not_congr (candidate order state root)) (not_congr (pending order state root))))

theorem rejection (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    B4TargetV6.RejectReason (boundary roles) first state root ↔ B4TargetV6.RejectReason (boundary roles) last state root := by
  unfold B4TargetV6.RejectReason
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  apply or_congr (candidate order state root)
  apply and_congr (not_congr (pending order state root))
  change ((∀ key children, ¬ GeneralNominalCenteredHeadCandidates.Survivor first _ root key children) ∨
    ∃ key children, GeneralNominalCenteredHeadCandidates.Unique first _ root key children ∧
      GeneralNominalCenteredHeadMatStepLocal.OutputConflict first state root key) ↔ _
  simp only [GeneralNominalCenteredHeadStepOrder.survivor order,GeneralNominalCenteredHeadStepOrder.unique order,conflict order]
  rfl

theorem local_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles) (frontier)
    (valid : Local first state root frontier) : Local last state root frontier := by
  cases valid with
  | pending known => exact .pending known
  | inspectionPending known waiting rootClear candidateClear =>
      exact .inspectionPending known ((pending order state root).mp waiting) rootClear
        ((not_congr (candidate order state root)).mp candidateClear)
  | rejected reason => exact .rejected ((rejection order state root).mp reason)
  | ambiguous ready one two different =>
      exact .ambiguous ((safe order state root).mp ready)
        ((GeneralNominalCenteredHeadStepOrder.survivor order _ root _ _).mp one)
        ((GeneralNominalCenteredHeadStepOrder.survivor order _ root _ _).mp two) different
  | selected ready only clear =>
      exact .selected ((safe order state root).mp ready)
        ((GeneralNominalCenteredHeadStepOrder.unique order _ root _ _).mp only)
        ((not_congr (conflict order state root _)).mp clear)

theorem local_iff (order : Reorders first last) (state : State roles) (root : Occurrence roles) (frontier) :
    Local first state root frontier ↔ Local last state root frontier :=
  ⟨local_forward order state root frontier,
    local_forward (GeneralRegistryChildOrder.reorders_symm order) state root frontier⟩

end Yulang.GeneralNominalCenteredHeadMatStepOrder
