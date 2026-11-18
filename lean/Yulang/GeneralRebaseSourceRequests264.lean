import Yulang.GeneralNominalVersionedMixedGrowth234
import Yulang.GeneralNominalVersionedMixedCommon235
import Yulang.GeneralRebaseRegisteredSites263
import Yulang.GeneralRebaseMultiSource263
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSourceRequests264
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralSourceState (Output)

/-- Concrete source data sufficient for growing live proposals. No finite
projection or desired semantic conclusion occurs in this condition. -/
structure Growth (before after : State roles) : Prop where
 plans : before.plans ⊆ after.plans
 requests : ∀ focus : Occurrence roles, ∀ output ∈ requests before.core focus,
   output ∈ requests after.core focus

/-- Plan-list identity and request membership identity, not request list
identity: list order and duplicates are deliberately not asserted equal. -/
structure Same (before after : State roles) : Prop where
 plans : before.plans = after.plans
 requests : ∀ focus : Occurrence roles, ∀ output : Output,
   output ∈ requests before.core focus ↔ output ∈ requests after.core focus

theorem Same.growth (same : Same before after) : Growth before after :=
 ⟨fun _ member => same.plans ▸ member,fun focus output member => (same.requests focus output).mp member⟩

theorem at_growth (action : At registry before focus after) : Growth before after := by
 have growth := GeneralNominalVersionedMixedGrowth234.at_growth action
 exact ⟨growth.plans,fun _ => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
   growth.legacy.rawSites growth.legacy.aliases⟩

theorem step_growth (action : Step registry root before after) : Growth before after :=
 at_growth action.choose_spec.2

theorem steps_growth (path : B4Target.Steps (Step registry root) before after) : Growth before after := by
 have growth := GeneralNominalVersionedMixedGrowth234.steps path
 exact ⟨growth.plans,fun _ => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
   growth.legacy.rawSites growth.legacy.aliases⟩

theorem refresh_same (state : State roles) (context : GeneralNominalCandidates.Context) :
 Same state (GeneralNominalVersionedRefresh232.refresh state context) :=
 ⟨rfl,fun _ _ => (GeneralNominalVersionedRefresh232.refresh_requests state context).symm⟩

theorem reobserve_same (state : State roles)
 (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
 Same state (GeneralNominalVersionedRefresh232.reobserve state revision) :=
 ⟨rfl,fun _ _ => (GeneralNominalVersionedRefresh232.reobserve_requests state revision).symm⟩

theorem equate_same (state : State roles) (first last : Nat) :
 Same state (GeneralNominalVersionedAdministrative232.equate state first last) :=
 ⟨rfl,fun _ _ => GeneralNominalVersionedRefresh232.requests_iff_of_same_lists rfl rfl⟩

theorem merge_growth (state : State roles) (first last : Site roles) :
 Growth state (GeneralNominalVersionedAdministrative232.merge state first last) :=
 ⟨fun _ member => member,fun _ => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
   (fun _ member => member) (fun _ member => List.mem_cons_of_mem _ member)⟩

theorem install_growth (state : State roles) (effect : Effect roles) :
 Growth state (GeneralNominalVersionedInstall232.install state effect) :=
 ⟨fun _ member => List.mem_cons_of_mem _ member,fun _ => GeneralNominalVersionedInstall232.requests_included state.core effect.plan⟩

theorem install_selected (state : State roles) (effect : Effect roles) :
 GeneralRebaseMultiSource263.selected (GeneralNominalVersionedInstall232.install state effect) =
 GeneralRebaseMultiSelection263.ofPlan effect.plan :: GeneralRebaseMultiSource263.selected state := rfl

theorem merge_selected (state : State roles) (first last : Site roles) :
 GeneralRebaseMultiSource263.selected (GeneralNominalVersionedAdministrative232.merge state first last) =
 GeneralRebaseMultiSource263.selected state := rfl

/-- Every retained versioned Plan has an actual present raw root identity on a
source path. This supplies the premise for existing source request conservation. -/
theorem registered_present (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (state : State roles)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (plan : Plan roles) (member : plan ∈ state.plans) :
 GeneralNominalCenteredHeadMatCompletionRequests.Present state.core plan.packet.site.occurrence.identity := by
 have input := GeneralRebaseRegisteredSites263.inputs registry context root state path plan member
 obtain ⟨raw,present,same⟩ :=
   (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).2.1 plan.input input
 exact ⟨raw,present,congrArg Occurrence.identity (same.trans plan.input_exact)⟩

theorem source_registered_present (registry : Registry) (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (plan : Plan roles) (member : plan ∈ state.plans) :
 GeneralNominalCenteredHeadMatCompletionRequests.Present state.core plan.packet.site.occurrence.identity := by
 obtain ⟨start,source,path⟩ := GeneralNominalVersionedMixedSourceBoundary234.reachable_compiled reachable
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := source
 exact registered_present _ context root state path plan member

/-- Actual source installation conserves requests at every OLD registered
Plan root. It does not say all arbitrary roots or newly emitted sites are old. -/
theorem source_install_old_requests (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (enabled : Installable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect)
 (plan : Plan roles) (member : plan ∈ state.plans) (output : Output) :
 output ∈ requests (GeneralNominalVersionedInstall232.install state effect).core plan.packet.site.occurrence ↔
 output ∈ requests state.core plan.packet.site.occurrence :=
 GeneralNominalVersionedMixedCommon235.requests_iff checked reachable enabled.registry_eq enabled.snapshot_eq
   (source_registered_present registry root state reachable plan member)
end Yulang.GeneralRebaseSourceRequests264
