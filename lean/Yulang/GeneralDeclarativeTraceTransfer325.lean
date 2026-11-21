import Yulang.GeneralDeclarativeTraceExpand323
import Yulang.GeneralDeclarativeOrigins321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTraceTransfer325
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeLowerKnown321 (alias_mono)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)

theorem lift_trace {s t : State} (normal : s.normal = t.normal)
    (sameRows : s.equations ⊆ t.equations) (proof : Trace s mode n code links) :
    Trace t mode n code links :=
  Trace.rec
    (motive_1 := fun mode n code links _ => Trace t mode n code links)
    (motive_2 := fun mode ns codes links _ => TraceArgs t mode ns codes links)
    (by intro _ _ _; exact .capture)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .primitive (alias_mono normal sameRows equal) (sameRows stored) ih)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .nominal (alias_mono normal sameRows equal) (sameRows stored) ih)
    (by intro _ _ _ _ _ _ _ _ _ _ equal stored _ _ ih jh; exact .record (alias_mono normal sameRows equal) (sameRows stored) ih jh)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .variant (alias_mono normal sameRows equal) (sameRows stored) ih)
    (by intro _ _ _ _ _ _ _ _ _ equal stored _ _ ih jh; exact .join (alias_mono normal sameRows equal) (sameRows stored) ih jh)
    (by intro _; exact .nil)
    (by intro _ _ _ _ _ _ _ _ _ ih jh; exact .cons ih jh)
    proof

theorem ordinary {s : State} (support : Supported s completed)
    (proof : Trace (restriction support) mode n code links) :
    Trace s mode n code links := by
  apply lift_trace (show (restriction support).normal = s.normal from rfl) ?_ proof
  intro row member
  obtain ⟨origin,proven,ready⟩ := (backed_iff support row).mp member
  exact support.ordinary proven

end Yulang.GeneralDeclarativeTraceTransfer325
