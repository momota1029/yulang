import Yulang.GeneralRebaseSourceSelect267
import Yulang.GeneralRebaseInstallChecks267
import Yulang.GeneralRebaseCheckedLocal266

namespace Yulang.GeneralRebaseSourceInstall267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseInstallChecks267 (choice choice_exact edgesRecorded missing_edge_proves_novel)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseMultiSelection263 (proposal ofPlan)
open GeneralRebaseCheckedWrite259 (commit)
open GeneralSourceState (Output)

theorem effect_ext (one two : Effect roles) (registry : one.registry = two.registry)
 (snapshot : one.snapshot = two.snapshot) (samePlan : one.plan = two.plan) : one = two := by
 cases one; cases two
 cases registry; cases snapshot; cases samePlan
 rfl

/-- The history guard is calculated over actual aliases and prior packets.
Unlike the cycle 264 sufficient condition, this does not restrict the
registry to one declaration key per role. The joint model is still genuine. -/
theorem installable_of_choice (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (effect : Effect roles) (registered : effect.registry = Encoded registry) (atState : effect.snapshot = state.core)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children))
 (choiceOK : choice state.core.erased.current effect.plan.packet = true)
 (common : ∃ model, Residual state effect model) : Installable (Encoded registry) state effect := by
 have frame := effect.frame
 rw [registered,atState] at frame
 have compiledSelected := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected
 obtain ⟨model,holds⟩ := common
 have operational := (GeneralNominalVersionedMixedMaterialization237.installation_models_iff
   checked reachable registered atState).mpr holds
 exact (GeneralNominalVersionedMixedGuardReduction235.installable_iff registered atState compiledSelected
   (GeneralNominalVersionedMixedEmbedding234.source_cache reachable)).mpr
   ⟨GeneralNominalVersionedMixedReady235.materialized reachable frame,
    (choice_exact ..).mp choiceOK,model,operational⟩

theorem source_step (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (effect : Effect roles) (registered : effect.registry = Encoded registry) (atState : effect.snapshot = state.core)
 (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children))
 (choiceOK : choice state.core.erased.current effect.plan.packet = true)
 (common : ∃ model, Residual state effect model)
 (novel : ¬ Committed state effect.plan) :
 (Boundary roles).Step registry root state (install state effect) ∧
 (∃ model, Models (install state effect) model) := by
 have enabled := installable_of_choice registry state root checked reachable effect registered atState selected choiceOK common
 obtain ⟨model,holds⟩ := enabled.common
 exact ⟨⟨_,generated,.install effect enabled novel⟩,model,(GeneralNominalVersionedInstall232.install_models atState).mpr holds⟩

theorem checked_projection (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (effect : Effect roles) (registered : effect.registry = Encoded registry) (atState : effect.snapshot = state.core)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children))
 (choiceOK : choice state.core.erased.current effect.plan.packet = true)
 (common : ∃ model, Residual state effect model)
 (owners : List Nat) (pool : List Output)
 (closed : liveFacts (install state effect) ⊆ GeneralRebaseCheckedLocal266.FiniteBasis owners pool) :
 let before := project owners pool state
 let after := project owners pool (install state effect)
 commit before (proposal state.core (ofPlan effect.plan)) =
  .ok (if after.remaining = before.remaining then none else some after) :=
 GeneralRebaseCheckedLocal266.checked_install registry checked root state reachable effect
  (installable_of_choice registry state root checked reachable effect registered atState selected choiceOK common) owners pool closed

end Yulang.GeneralRebaseSourceInstall267
