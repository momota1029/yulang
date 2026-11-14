import Yulang.GeneralNominalCenteredHeadAllocCollisionLocal

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocCollision
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadAllocCollisionSource GeneralNominalCenteredHeadAllocCollisionLocal
open GeneralNominalCenteredHeadMatEffects GeneralNominalCenteredHeadMatExpressions CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatStepJournal

theorem canonical_declaration : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_pair,
    declaration,GeneralNominalCenteredHeadAllocEncoding.declaration,GeneralNominalCenteredHeadAllocEncoding.clause]

theorem schema_exact : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨firstTarget,.actual,.primitive (.scalar .int) []⟩,
      ⟨lastTarget,.actual,.variant 0 (.primitive (.scalar .int) [])⟩],false⟩ := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical_declaration]
  change GeneralNominalCenteredHeadMatSchemas.generated GeneralDeclarationExamples.constructors
    GeneralNominalExamples.interpretation _ = _
  simp only [declaration,GeneralNominalCenteredHeadAllocEncoding.declaration,List.map_cons,List.map_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalCenteredHeadMatSchemas.emissionRequests,List.ofFn_zero,
    GeneralNominalCenteredHeadMatSchemas.generated,GeneralNominalCenteredHeadMatSchemas.materialize,
    GeneralNominalCenteredHeadMatSchemas.Schema.append,
    GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_translation,
    GeneralNominalCenteredHeadMatCompletionCollisionPackets.variant_translation,
    GeneralDeclarationDemands.outputTarget,normalize,normalizeArgs,GeneralNominalAllocation.allocation,
    declaration,GeneralNominalCenteredHeadAllocEncoding.declaration,GeneralNominalCenteredHeadAllocEncoding.clause,
    GeneralNominalCenteredHeadAllocEncoding.equation,firstTarget,lastTarget,GeneralNominalDemandMerging.pointSite,
    List.attach_cons,List.attach_nil]

theorem model_first : (model firstTarget).1 = .base .int := by
  have nonzero : firstTarget ≠ 0 := by have larger := first_above_seed; omega
  change (if firstTarget = lastTarget then _ else GeneralNominalCenteredHeadMatCompletionCollisionSource.model firstTarget).1 = _
  rw [ite_eq_right targets_distinct]
  change (if firstTarget = 0 then nominal 0 [.inl (.base .int)] else (.base .int : Ty)) = _
  exact ite_eq_right nonzero

theorem model_last : (model lastTarget).1 = variant 0 (.base .int) := by
  simp only [GeneralNominalCenteredHeadAllocCollisionSource.model,ite_true]

theorem outputs : GeneralNominalCenteredHeadMatStepPackets.Outputs plan model := by
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs
  rw [schema_exact]
  intro equation member
  rcases List.mem_cons.mp member with rfl | member
  · change Equivalent (model firstTarget).1 (.base .int)
    rw [model_first]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · cases List.mem_singleton.mp member
    change Equivalent (model lastTarget).1 (variant 0 (.base .int))
    rw [model_last]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_models : GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
  refine ⟨source_model,?_,outputs⟩
  refine ⟨((GeneralNominalPacketSupport.private_exact packet model).mp head_model.1).2,
    head_model.2,head_equations.1,?_,head_equations.2.2,?_,?_⟩
  · intro name needed
    rcases needed with input | ⟨clause,member,used⟩
    · change name ∈ ([] : List Nat) at input; cases input
    · have empty : clause.arguments = [] := by
        change clause ∈ [firstClause,lastClause] at member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · cases List.mem_singleton.mp member; rfl
      rw [empty] at used
      cases used
  · exact fun equation member _ => outputs equation member
  · intro clause member valid
    change clause ∈ [firstClause,lastClause] at member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨fun index => Fin.elim0 index,?_⟩
      change ∀ equation ∈ ([] : List GeneralNominalCenteredHeadMatSchemas.Equation), _
      intro equation present; cases present
    · cases List.mem_singleton.mp member
      refine ⟨fun index => Fin.elim0 index,?_⟩
      change ∀ equation ∈ ([] : List GeneralNominalCenteredHeadMatSchemas.Equation), _
      intro equation present; cases present

theorem installation_models : InstallationModels start effect model :=
  (GeneralNominalCenteredHeadMatCompletionLive.installation_models_iff checked compiled_reachable rfl rfl model).mpr
    ⟨inhabited,packet_models,effect_model.2⟩

theorem installable : GeneralNominalCenteredHeadMatStepKernel.Installable registry start effect := by
  apply (GeneralNominalCenteredHeadMatStepAvailability.selected_installable_iff compiled_reachable selected rfl rfl).mpr
  refine ⟨?_,GeneralNominalCenteredHeadAllocCollisionSource.model,installation_models⟩
  intro prior member; cases member

theorem children_length : children.length = 2 := by
  change packet.children.length = 2
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_declaration]
  simp [GeneralDeclarationDemands.emitAll,declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]

theorem novel : ¬ GeneralNominalCenteredHeadMatStepKernel.Committed start plan := by
  intro committed
  have nonempty : children ≠ [] := by
    intro empty
    have count := children_length
    rw [empty] at count
    contradiction
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact List.not_mem_nil (committed.2 child member)

abbrev finish := install start effect

theorem step : GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root start finish :=
  ⟨root,.root,.install effect installable novel⟩

theorem both_generated : ∀ child ∈ children,
    GeneralNominalSaturationState.Generated finish.core.erased.current root child :=
  fun _child member => .child .root (installed_child member)

theorem final_models : Models finish model := (install_models rfl).mpr installation_models

theorem collision_repaired :
    (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Checked sourceRegistry ∧
    (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Initial sourceRegistry root start ∧
    GeneralNominalCenteredHeadAllocBoundary.Local sourceRegistry start root (.selected 37 children) ∧
    GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root start finish ∧
    Models finish model ∧ children.length = 2 ∧
    ∀ child ∈ children, GeneralNominalSaturationState.Generated finish.core.erased.current root child :=
  ⟨⟨rfl,GeneralNominalCenteredHeadMatCompletionCollisionSource.checked⟩,initial_source,source_selected,
    step,final_models,children_length,both_generated⟩

end Yulang.GeneralNominalCenteredHeadAllocCollision
