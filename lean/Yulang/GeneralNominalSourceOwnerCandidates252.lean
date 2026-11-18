import Yulang.GeneralNominalOwnerCandidates252
import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralNominalPointErasure240
namespace Yulang.GeneralNominalSourceOwnerCandidates252
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalVersionedMixedKernel234
open GeneralNominalOwnerCandidates252

/-- One finite owner list works for all later mixed-source installations from
this actual initial source; no finite-depth premise is added. -/
theorem mixed_finite_owners (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ keys : List (Nat × Nat), ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ effect,
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state effect →
 ¬ Committed state effect.plan →
 (effect.plan.packet.site.occurrence.identity,effect.plan.packet.declaration.id) ∈ keys := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 refine ⟨owners (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry)
   context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels),?_⟩
 intro state path effect generated enabled novel
 exact installed_owner_enumerated formed point ground coverage path generated enabled novel

/-- I45 point-preserving source paths erase into the same mixed-source path,
so the finite owner list does not need a new measure assumption. -/
theorem point_finite_owners (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalPointSourceBoundary240.boundary roles).Initial sourceRegistry root start) :
 ∃ keys : List (Nat × Nat), ∀ state,
 B4Target.Steps ((GeneralNominalPointSourceBoundary240.boundary roles).Step sourceRegistry root) start state →
 ∀ effect,
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state effect →
 ¬ Committed state effect.plan →
 (effect.plan.packet.site.occurrence.identity,effect.plan.packet.declaration.id) ∈ keys := by
 have mixed : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start := source
 obtain ⟨keys,finite⟩ := mixed_finite_owners sourceRegistry root start mixed
 refine ⟨keys,?_⟩
 intro state path effect generated enabled novel
 exact finite state (GeneralNominalPointErasure240.steps_old path) effect generated enabled novel
end Yulang.GeneralNominalSourceOwnerCandidates252
