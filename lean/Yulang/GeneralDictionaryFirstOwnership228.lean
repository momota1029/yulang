import Yulang.GeneralDictionaryCapturedOwnership228
import Yulang.GeneralDictionaryMergeOwnership228

namespace Yulang.GeneralDictionaryFirstOwnership228
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227
open GeneralDictionaryCapturedOwnership228 (capturedSources Owned)
open GeneralDictionaryResidualOwnership228 (LocalMerge)
open GeneralNominalAllocation GeneralNominalAllocationSupport
open GeneralDictionaryRelativeProvenance226 (localSources)
variable {roles : Roles.RoleDecls}

theorem binding_endpoints (plan : Plan roles) : Endpoints plan.packet.bindings (capturedSources plan) := by
  intro binding member
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings plan] at member
  obtain ⟨capture,present,rfl⟩ := List.mem_map.mp member
  constructor
  · exact List.mem_flatMap.mpr ⟨capture,present,by simp⟩
  · exact List.mem_flatMap.mpr ⟨capture,present,by simp⟩

theorem merge_sources (plan : Plan roles) :
    GeneralDictionaryReachablePacket226.mergeSources plan ⊆ capturedSources plan ++ localSources plan := by
  intro name member
  obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp member
  have supported := binding_endpoints plan
  apply GeneralDictionaryHeadSharingRawSupport220.merges_sources_tight plan.packet.context.state
    (pool := capturedSources plan ++ localSources plan) _ _ atom present within
  · intro binding present
    exact ⟨List.mem_append_left _ (supported binding present).1,
      List.mem_append_left _ (supported binding present).2⟩
  · intro name declared
    exact GeneralDictionaryHeadSharingRawSupport220.capture_targets_local
      plan.packet.context.state supported declared

theorem merge_owned (plan : Plan roles)
    (member : identity ∈ GeneralDictionaryReachablePacket226.mergeSources plan) : Owned plan identity := by
  rcases List.mem_append.mp (merge_sources plan member) with captured | localName
  · exact Or.inl captured
  · obtain ⟨name,_,within⟩ := List.mem_flatMap.mp localName
    exact Or.inr ⟨name,by simpa [localSources,GeneralDictionaryHeadSharingRawSupport220.localTargets,GeneralNominalAllocation.source,GeneralNominalCenters.fresh,GeneralNominalAllocation.origin] using within⟩

theorem residual_owned
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryFirstResidual227.ResidualSources plan) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  rcases List.mem_append.mp member with mergeEmitted | child
  · rcases List.mem_append.mp mergeEmitted with merges | emitted
    · exact merge_owned plan merges
    · exact GeneralDictionaryCapturedOwnership228.emitted_residual_owned source path plan frame mergePurpose emitted
  · exact GeneralDictionaryCapturedOwnership228.child_sources_owned plan mergePurpose child

/-- A first protected p0/p1 occurrence belongs either to an actual captured
endpoint of that installation or its exact local aggregate key. -/
theorem first_owned
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root state pool)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before prior, ∃ effect : Effect roles,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Installable registry before effect ∧
      Contribution registry root before (install before effect)
        (GeneralDictionaryOriginJournal227.installDelta before effect) ∧
      Owned effect.plan (fresh context.state.seed invocation declaration purpose owner position) ∧
      B4Target.Steps (Step registry root) (install before effect) state := by
  obtain ⟨before,prior,effect,history,absent,enabled,event,member,suffix⟩ :=
    GeneralDictionaryFirstResidual227.first_merge_residual source trace mergePurpose present
  have frame := GeneralDictionaryDefaultDepth208.frame enabled
  have seed : effect.plan.packet.context.state.seed = context.state.seed :=
    (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
      (GeneralDictionaryDefaultDepth208.configuration_trace history.path).1
  have owned : Owned effect.plan (fresh context.state.seed invocation declaration purpose owner position) := by
    rw [← seed] at member ⊢
    exact residual_owned source history.path effect.plan frame mergePurpose member
  exact ⟨before,prior,effect,history,absent,enabled,event,owned,suffix⟩
end Yulang.GeneralDictionaryFirstOwnership228
