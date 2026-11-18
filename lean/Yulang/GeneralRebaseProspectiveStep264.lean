import Yulang.GeneralRebaseProspectiveCurrent264
import Yulang.GeneralNominalSourceOwnerCandidates252
namespace Yulang.GeneralRebaseProspectiveStep264
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232

/-- A real source step, not a historical-plan table write. The one-key-per-role
restriction derives choice; all remaining semantic obligations share one model. -/
theorem role_unique_step
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (reg : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
 (snapshot : effect.snapshot = state.core)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children))
 (uniqueRole : ∀ a ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∀ b ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations, a.role = b.role → a.id = b.id)
 (common : ∃ model, GeneralNominalVersionedMixedMaterialization237.Residual state effect model)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (novel : ¬ GeneralNominalVersionedInstallStep232.Committed state effect.plan) :
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root state
   (GeneralNominalVersionedInstall232.install state effect) ∧
 (∃ model, Models (GeneralNominalVersionedInstall232.install state effect) model) ∧
 effect.plan ∈ (GeneralNominalVersionedInstall232.install state effect).plans := by
 have current := GeneralRebaseProspectiveCurrent264.role_unique_current checked reachable effect reg snapshot selected uniqueRole common
 have enabled := GeneralNominalVersionedMixedCurrentCandidate235.source_installable current reachable selected
 refine ⟨⟨_,generated,.install effect enabled novel⟩,?_,List.mem_cons_self⟩
 obtain ⟨model,valid⟩ := enabled.common
 exact ⟨model,(GeneralNominalVersionedInstall232.install_models snapshot).mpr valid⟩

/-- The finite prospective-owner list is fixed at source initialization, before
choosing any future candidate, common model or installation path. -/
theorem source_finite_steps
 (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (uniqueRole : ∀ a ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∀ b ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations, a.role = b.role → a.id = b.id) :
 ∃ keys : List (Nat × Nat), ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start state →
 ∀ (effect : Effect roles),
 effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry → effect.snapshot = state.core →
 ∀ children, GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children) →
 (∃ model, GeneralNominalVersionedMixedMaterialization237.Residual state effect model) →
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 ¬ GeneralNominalVersionedInstallStep232.Committed state effect.plan →
 (effect.plan.packet.site.occurrence.identity,effect.plan.packet.declaration.id) ∈ keys ∧
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root state
   (GeneralNominalVersionedInstall232.install state effect) ∧
 (∃ model, Models (GeneralNominalVersionedInstall232.install state effect) model) ∧
 effect.plan ∈ (GeneralNominalVersionedInstall232.install state effect).plans := by
 obtain ⟨keys,covered⟩ := GeneralNominalSourceOwnerCandidates252.mixed_finite_owners registry root start source
 refine ⟨keys,?_⟩
 intro state path effect reg snapshot children selected common generated novel
 have reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state :=
   ⟨start,source,path⟩
 have current := GeneralRebaseProspectiveCurrent264.role_unique_current checked reachable effect reg snapshot selected uniqueRole common
 have enabled := GeneralNominalVersionedMixedCurrentCandidate235.source_installable current reachable selected
 exact ⟨covered state path effect generated enabled novel,
   role_unique_step checked reachable effect reg snapshot selected uniqueRole common generated novel⟩
end Yulang.GeneralRebaseProspectiveStep264
