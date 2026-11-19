import Yulang.GeneralRebaseCheckedLocal266
import Yulang.GeneralRebaseProspectiveStep264

namespace Yulang.GeneralRebaseProspectiveChecked266
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseMultiSelection263 (ofPlan proposal)
open GeneralRebaseCheckedWrite259 (commit)

/-- One source-derived finite basis works for every guarded prospective install.
The selection, unique-role restriction, common residual model, and novelty are
inputs; the result does not search for them or decide source satisfiability. -/
theorem source_checked_installs (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (uniqueRole : ∀ a ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∀ b ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations, a.role = b.role → a.id = b.id) :
 ∃ owners : List Nat, ∃ pool : List GeneralSourceState.Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start state →
 ∀ (effect : Effect roles),
 effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry → effect.snapshot = state.core →
 ∀ children, GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children) →
 (∃ model, GeneralNominalVersionedMixedMaterialization237.Residual state effect model) →
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 ¬ GeneralNominalVersionedInstallStep232.Committed state effect.plan →
 let installed := GeneralNominalVersionedInstall232.install state effect
 let before := project owners pool state
 let after := project owners pool installed
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root state installed ∧
 (∃ model, Models installed model) ∧
 commit before (proposal state.core (ofPlan effect.plan)) =
   .ok (if after.remaining = before.remaining then none else some after) := by
 obtain ⟨owners,pool,covered⟩ := GeneralRebaseLiveProjection264.source_covered registry root start source
 refine ⟨owners,pool,?_⟩
 intro state path effect reg snapshot children selected common generated novel
 have reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state :=
   ⟨start,source,path⟩
 have current := GeneralRebaseProspectiveCurrent264.role_unique_current checked reachable effect reg snapshot selected uniqueRole common
 have enabled := GeneralNominalVersionedMixedCurrentCandidate235.source_installable current reachable selected
 obtain ⟨step,model,_⟩ := GeneralRebaseProspectiveStep264.role_unique_step checked reachable effect reg snapshot selected uniqueRole common generated novel
 exact ⟨step,model,GeneralRebaseCheckedLocal266.checked_install registry checked root state reachable effect enabled owners pool
   (covered _ (.tail path step))⟩

end Yulang.GeneralRebaseProspectiveChecked266
