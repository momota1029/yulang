import Yulang.GeneralDictionaryNominalSharedDiscovery179

/-! Shared-name current-model residuals at arbitrary outer endpoint slots.
Point and nonpoint sources use the same explicit sharing/merge obligation. -/
namespace Yulang.GeneralDictionaryCenteredSharedAny179
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176
theorem point_shape_exists (state : GeneralNominalState.State) (name : Nat)
    (names : Fin n → Nat) (slot : Fin state.base.slots) (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name (List.ofFn fun i => .variables [names i]))
      (slot,slot) origin)) :
    ∃ (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (bounds : Fin n → GeneralNominalInspection.Bounds state),
      state.nominals slot = some descriptor ∧ descriptor.declaration.name = name ∧
      descriptor.arguments = List.ofFn fun i => .type (bounds i) := by
  simp only [inspect] at finished
  split at finished
  · split at finished <;> simp [Finished,block,Report.visit] at finished
  · rename_i descriptor recorded
    split at finished
    · rename_i sameName
      split at finished
      · simp [Finished,block,Report.visit] at finished
      · rename_i arguments found
        simp only [↓reduceIte] at finished
        have len := GeneralDictionaryNominalPairDiscovery178.many_length state _ arguments _ _ finished
        have length : n = arguments.length := by simpa using len
        let bounds : Fin n → GeneralNominalInspection.Bounds state := fun i => arguments[i.val]'(by omega)
        have bounds_eq : List.ofFn bounds = arguments := by
          apply List.ext_getElem
          · simp [length]
          · intro i hi hj; simp [bounds]
        have parameters := GeneralDictionary171InputDiscovery.type_arguments_exact descriptor.arguments arguments found
        have exactParameters : descriptor.arguments = List.ofFn fun i => GeneralNominalState.Parameter.type (bounds i) := by
          rw [parameters,← bounds_eq,List.map_ofFn]
          rfl
        exact ⟨descriptor,bounds,recorded,sameName,exactParameters⟩
    · simp [Finished,Report.visit] at finished
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

theorem point_holds_iff_shared_merges
    (candidate : Candidate registry state focus key children plan)
    (slot : Fin plan.packet.context.state.base.slots)
    (name : Nat) (names : Fin n → Nat)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔
      GeneralNominalSharedCaptureFacts.Coherent model (plan.packet.context.state.base.source slot) name names ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity plan.packet.declaration
          (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds))) := by
  obtain ⟨_,_,_,bounds,found,finished,_,_⟩ := candidate.prepared
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  have fi : Finished (inspect plan.packet.context.state (.nominal name (List.ofFn fun i => .variables [names i]))
      (slot,slot) none) := by
    simpa only [Finished,report,query,inspectMany,Report.append,List.append_nil] using finished
  obtain ⟨descriptor,bounds,recorded,head,parameters⟩ := point_shape_exists _ name names slot none fi
  have source : GeneralNominalState.Models plan.packet.context.state model := by
    rw [candidate.context_eq]; exact valid.1.1
  have packetBounds := Option.some.inj (candidate.located.symm.trans located)
  change BranchModels _ _ _ _ _ _ _ ↔ _
  rw [packetBounds,GeneralNominalSharedCaptureFacts.branch_models_iff_residual plan.packet.context
    plan.packet.registry plan.packet.site.occurrence plan.packet.declaration plan.packet.checked
    slot descriptor recorded names bounds parameters (by rw [head]; exact query) model]
  rw [head,GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ terminal outputs]
  exact ⟨fun given => ⟨given.2.1,given.2.2.1⟩,
    fun given => ⟨source,given.1,given.2,GeneralNominalMaterialization.empty_models ..⟩⟩

theorem holds_iff_shared_merges
    (candidate : Candidate registry state focus key children plan)
    (lower upper : Fin plan.packet.context.state.base.slots)
    (name : Nat) (names : Fin n → Nat)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(lower,upper)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    plan.packet.Holds model ↔
      GeneralNominalSharedCaptureFacts.Coherent model (plan.packet.context.state.base.source lower) name names ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity plan.packet.declaration
          (bindings plan.packet.context.state (report plan.packet.context plan.packet.declaration plan.packet.bounds))) := by
  by_cases same : lower = upper
  · subst upper
    exact point_holds_iff_shared_merges candidate lower name names query located terminal outputs model valid
  · exact GeneralDictionaryNominalSharedDiscovery179.candidate_holds_iff_shared_merges candidate
      lower upper same name names query located terminal outputs model valid

end Yulang.GeneralDictionaryCenteredSharedAny179
