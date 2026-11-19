import Yulang.GeneralRebaseCompactInstallGuard279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseCompactObservationGuard279
open GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges models_exact)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseCompactTrust279 (cache_iff)
open GeneralNominalVersionedMixedObservations233 (Refresh Reobserve)
open GeneralNominalReobservationSteps (Revision Improves)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}

def refreshForward {context} (cert : Refresh state context) :
    Refresh (replaceEdges state new) context :=
  ⟨cert.refines,cert.interpretation,cert.support,
    fun _ h => cert.constraints _ ((models_exact state new _).mp h),
    (cache_iff _).mpr cert.cache⟩

def revisionForward (rev : Revision state.core.erased.current) :
    Revision (replaceEdges state new).core.erased.current :=
  ⟨rev.entries,rev.catalogue,rev.opaqueHeads,rev.domain⟩

theorem snapshot_eq (rev : Revision state.core.erased.current) :
    (revisionForward (new := new) rev).snapshot = rev.snapshot := rfl

theorem improves {rev : Revision state.core.erased.current} (h : Improves rev) :
    Improves (revisionForward (new := new) rev) := h

theorem certificate {rev : Revision state.core.erased.current} (cert : Reobserve state rev) :
    Reobserve (replaceEdges state new) (revisionForward rev) :=
  ⟨cert.raw,(cache_iff _).mpr cert.cache⟩

end Yulang.GeneralRebaseCompactObservationGuard279
