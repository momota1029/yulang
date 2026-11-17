import Yulang.GeneralNominalVersionedMixedCenters237
import Yulang.GeneralNominalVersionedTraceSupport237
/-! A fixed finite center-identity cover for all futures of every actual source
state. Initial ground/point/coverage witnesses are obtained from the boundary,
not added as caller assumptions. Versioned endpoint/slot finiteness is separate. -/
namespace Yulang.GeneralNominalVersionedSourceCenters237
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedKernel234
variable {roles : Roles.RoleDecls}

theorem initial_cover
 (formed : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ identities : List Nat, ∀ state,
 B4Target.Steps (Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root) start state →
 ∀ site ∈ state.core.sites, site.occurrence.identity ∈ identities := by
 obtain ⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩ := formed
 subst start
 subst legacy
 exact GeneralNominalVersionedMixedCenters237.identity_cover
   (GeneralNominalCenteredHeadAllocEncoding.initial_source source) point ground
   (GeneralNominalCenteredHeadAllocEncoding.coverage coverage)

theorem reachable_cover
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
 ∃ identities : List Nat, ∀ after,
 B4Target.Steps (Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root) state after →
 ∀ site ∈ after.core.sites, site.occurrence.identity ∈ identities := by
 obtain ⟨initial,formed,history⟩ := path
 obtain ⟨identities,covered⟩ := initial_cover formed
 exact ⟨identities,fun after future => covered after (GeneralNominalVersionedTraceSupport237.append_steps history future)⟩

theorem current_cover
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
 ∃ identities : List Nat, ∀ site ∈ state.core.sites, site.occurrence.identity ∈ identities := by
 obtain ⟨identities,covered⟩ := reachable_cover path
 exact ⟨identities,covered state .refl⟩
theorem generated_cover
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
 ∃ identities : List Nat, ∀ after,
 B4Target.Steps (Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root) state after →
 ∀ demand, GeneralNominalSaturationState.Generated after.core.erased.current root demand →
 demand.identity ∈ identities := by
 obtain ⟨identities,covered⟩ := reachable_cover path
 refine ⟨identities,?_⟩
 intro after future demand generated
 have reach : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root after := by
   obtain ⟨initial,formed,history⟩ := path
   exact ⟨initial,formed,GeneralNominalVersionedTraceSupport237.append_steps history future⟩
 obtain ⟨center,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_center reach generated
 have result := covered after future center member
 rw [same] at result
 exact result

end Yulang.GeneralNominalVersionedSourceCenters237
