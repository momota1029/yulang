import Yulang.GeneralVersionedCompiledFirstInstall313

set_option backward.isDefEq.respectTransparency false
/-! The original source's closed ground arguments certify current root
constructor tests even after actual changes in packet, cache, and alias history. -/
namespace Yulang.GeneralVersionedReachableRootGround313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedSharingBinderRows313 (Tests)
open GeneralNominalGroundAccessibility (Inputs root_inputs)
open GeneralNominalCommonBridge (Assignment)

theorem ground {s : State roles} {root : Occurrence roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core root key p)
    (m : Assignment) (valid : Models s m) :
    ∃ ctx labels, Inputs ctx m p.input.observed labels := by
  obtain ⟨start,⟨legacy,⟨ctx,labels,formation,point,sourceGround,cover,rfl⟩,rfl⟩,steps⟩ := actual
  have actual : Reachable registry root s :=
    ⟨_,⟨_,⟨ctx,labels,formation,point,sourceGround,cover,rfl⟩,rfl⟩,steps⟩
  have rootSitePresent : rootSite ctx.state.seed root ∈ s.core.sites :=
    GeneralNominalVersionedMixedGrowth234.steps_sites steps (List.mem_singleton_self _)
  have same := GeneralVersionedCurrentFrame312.center_exact checked actual p.input _
    frame.center_recorded rootSitePresent (p.input_exact.trans frame.occurrence_eq)
  have observed : (rootSite ctx.state.seed root).observed = GeneralNominalDemandMerging.pointSite root :=
    GeneralNominalCenteredPointSource.point_observed _ point (point_center _ _)
  have keep := valid.1.2.1
  rw [GeneralNominalVersionedMixedGrowth234.steps_source steps] at keep
  refine ⟨ctx,labels,?_⟩
  rw [same,observed]
  exact root_inputs sourceGround point m keep

theorem tests {s : State roles} {p : Plan roles}
    (checked : (boundary roles).Checked registry)
    (actual : Reachable registry root s)
    (frame : Frame (Compiled registry) s.core root key p)
    (m : Assignment) (valid : Models s m) :
    Tests p m := by
  obtain ⟨_,_,observed⟩ := ground checked actual frame m valid
  exact GeneralVersionedFirstGroundHead313.tests_of_registered_ground frame m valid observed

end Yulang.GeneralVersionedReachableRootGround313
