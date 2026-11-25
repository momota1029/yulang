import Yulang.GeneralDeclarativeI65I75ProjectedEventSource426
import Yulang.GeneralDeclarativeI65I75ActualOutputWire425
import Yulang.GeneralDeclarativeI65I75ProjectedCoreReadback425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open ProjectedCore425
open Checker408 (Problem)
open RecordEndpoints422 (Read ProjectedOutput readEndpoints422 readProjectedOutput422)
open CommonNominalFullCarrier (Ty Equivalent)

/-- Source construction ignores the target retention proof entirely.
The head is obtained from this literal B6 output, so the dispatch
cannot align a different authored witness at the same integer labels. -/
def projectedLeafOfRead426 {p : Problem} (r : Read p) (b : ProjectedOutput r) :
    OriginalProjectedLeaf426 p.state.core p.state.b6 p.root :=
  let o := coreOutputFromSource425 r b
  ⟨r.outIndex,r.exactOut,o,r.checked,r.endpointsApart,r.noWhere,r.noOutBinders,r.actualAssoc,r.rawSafe⟩

def readProjectedLeafSource426 (p : Problem) (wire : RecordEndpoints422.Wire) :
    Option (OriginalProjectedLeaf426 p.state.core p.state.b6 p.root) := do
  let r ← readEndpoints422 p wire
  let b ← readProjectedOutput422 r
  pure (projectedLeafOfRead426 r b)

theorem projected_leaf_root_guard_is_exact426 (p : Problem) :
    OriginalRootCycle426 p.state.core p.root ↔ RootCycle p.state p.root := Iff.rfl

theorem original_projected_leaf_uses_identical_core425_426 {p : Problem}
    (w : PreparedWrite p) : (projectedLeafOfRead426 w.original w.typed).out =
      originalProjectedCoreOutput425 w := rfl

/-- The earlier exact required-channel read is a conservative producer of
the new acyclic certificate, at the same original ordinary addresses. -/
def requiredRowsOf423_426 {p : Problem} {r : Read p} (b : ProjectedOutput r)
    (keep : RequiredOnlyRetained r) : RequiredRetention426 (projectedLeafOfRead426 r b).out :=
  ⟨keep.field,keep.targetOrdinal,keep.lowerOrdinal,keep.upperOrdinal,
    keep.atTarget,keep.atLower,keep.atUpper⟩

theorem exact_old_required_rows_replay_into_new_core426 {p : Problem} {r : Read p}
    (b : ProjectedOutput r) (keep : RequiredOnlyRetained r) :
    readRequiredRetention426 (projectedLeafOfRead426 r b).out
      ⟨keep.targetOrdinal,keep.lowerOrdinal,keep.upperOrdinal⟩ =
        some (requiredRowsOf423_426 b keep) :=
  exact_required_rows_are_read426 (requiredRowsOf423_426 b keep)

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
