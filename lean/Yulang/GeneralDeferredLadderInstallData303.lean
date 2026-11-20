import Yulang.GeneralNominalVersionedInstallation231
import Yulang.GeneralNominalCenteredHeadMatPlanData

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderInstallData303
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same occurrence bindings)
open GeneralNominalVersionedInstallation231 (reserved allocated atoms)
open GeneralNominalReportErasure (Data checks_exact)

theorem reserved_eq {p q : Plan roles} (same : Same p q) :
    reserved p.packet = reserved q.packet := by
  unfold reserved GeneralNominalVersionedAllocation231.reserved
  rw [same.registry,occurrence same,bindings same]
  rw [same.seed]

theorem allocated_eq {p q : Plan roles} (same : Same p q) :
    allocated p.packet = allocated q.packet := by
  unfold allocated
  rw [same.registry,occurrence same,bindings same]

theorem atoms_eq {p q : Plan roles} (same : Same p q) :
    atoms p.packet = atoms q.packet := by
  have checks := congrArg Data.selfChecks same.report
  simp only [checks_exact] at checks
  unfold atoms GeneralNominalVersionedAllocation231.merges
  rw [bindings same,same.registry,occurrence same,same.declaration,checks]
  unfold GeneralNominalVersionedAllocation231.capture GeneralNominalAllocation.source
  rw [same.seed]

end Yulang.GeneralDeferredLadderInstallData303
