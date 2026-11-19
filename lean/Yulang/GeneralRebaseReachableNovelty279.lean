import Yulang.GeneralRebaseInstallNovelty279
import Yulang.GeneralNominalVersionedMixedCommon235
import Yulang.GeneralNominalVersionedMixedProgressSplit236

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReachableNovelty279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralNominalVersionedMixedKernel234 (Committed Installable Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseInstallNovelty279 (Covered FreshChild FullSilent LostModel)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
variable {state : State roles} {e : Effect roles}

theorem source_models_iff (checked : (boundary roles).Checked r)
    (reached : Reachable r root state) (aligned : e.registry = registry r)
    (snapshot : e.snapshot = state.core) (m : Assignment) :
    Models (install state e) m ↔
      Models state m ∧ GeneralNominalVersionedPlans231.Holds e.plan m ∧ e.Live state.core m :=
  (install_models snapshot).trans
    (GeneralNominalVersionedMixedCommon235.installation_models_iff checked reached aligned snapshot)

theorem committed_iff (checked : (boundary roles).Checked r)
    (reached : Reachable r root state) (aligned : e.registry = registry r)
    (snapshot : e.snapshot = state.core) :
    Committed state e.plan ↔ FullSilent state e ∧ Covered state e.plan := by
  constructor
  · rintro ⟨oldModel,children⟩
    refine ⟨?_,children⟩
    intro m
    rw [source_models_iff checked reached aligned snapshot]
    exact ⟨And.left,fun stateModel => ⟨stateModel,oldModel m stateModel⟩⟩
  · rintro ⟨same,children⟩
    exact GeneralRebaseInstallNovelty279.committed_of_silent snapshot same children

theorem uncommitted_iff (checked : (boundary roles).Checked r)
    (reached : Reachable r root state) (aligned : e.registry = registry r)
    (snapshot : e.snapshot = state.core) :
    ¬ Committed state e.plan ↔ LostModel state e ∨ FreshChild state e.plan := by
  constructor
  · exact GeneralRebaseInstallNovelty279.install_dichotomy snapshot
  · rintro (lost | fresh) done
    · exact ((GeneralRebaseInstallNovelty279.no_loss_iff snapshot).mp
        ((committed_iff checked reached aligned snapshot).mp done).1) lost
    · exact GeneralRebaseInstallNovelty279.novel_child_blocks (effect := e) fresh done

theorem qualifying_install (checked : (boundary roles).Checked r)
    (reached : Reachable r root state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root e.plan.packet.site.occurrence)
    (enabled : Installable (registry r) state e)
    (changePresent : LostModel state e ∨ FreshChild state e.plan) :
    Step (registry r) root state (install state e) :=
  ⟨_,generated,.install e enabled ((uncommitted_iff checked reached enabled.registry_eq enabled.snapshot_eq).mpr changePresent)⟩

end Yulang.GeneralRebaseReachableNovelty279
