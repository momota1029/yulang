import Yulang.GeneralDeclarativeCurrentResult330
import Yulang.GeneralDeclarativeGuardView330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeGuardCurrent330
open GeneralDeclarativeArityFixture330 (returnRow childRow interp)
open GeneralDeclarativeArityProbe330 (source)
open GeneralDeclarativeCurrentResult330 (receipt reverseReceipt)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeOutputOrigins323 (emit backed_unchanged)
open GeneralDeclarativeGuardView330 (using_receipt positive_exact)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeRepeatDecl327 (reg)

abbrev unavailable (_ : Nat) : Prop := False
abbrev prior := GeneralDeclarativeArityProbe330.support unavailable
abbrev now := GeneralDeclarativeCurrentProbe330.support unavailable

theorem authorized_exact (e : Equation) :
    e ∈ (restriction prior).equations ↔ e ∈ (restriction now).equations := by
  have old := (backed_unchanged (emit (source unavailable) 1 [returnRow]) [childRow]
      (owner := 2) (fun h => h) e).trans (backed_unchanged (source unavailable) [returnRow]
      (owner := 1) (fun h => h) e)
  have seen := (backed_unchanged (emit (source unavailable) 1 [GeneralDeclarativeCurrentProbe330.returnRow])
      [childRow] (owner := 2) (fun h => h) e).trans (backed_unchanged (source unavailable)
      [GeneralDeclarativeCurrentProbe330.returnRow] (owner := 1) (fun h => h) e)
  exact old.trans seen.symm

/-- Equivalence of supported readiness and positive probes follows
from actual shared origins and checked ordinary bounds, not from
mere agreement on the classes of satisfying models. -/
theorem actual_guards (goal : GeneralDeclarativeDemand320.Demand) :
    (Ready prior goal ↔ Ready now goal) ∧
    ∀ impl, HeadMatches (restriction prior) reg.constructors interp goal impl ↔
      HeadMatches (restriction now) reg.constructors interp goal impl :=
  positive_exact (using_receipt receipt (fun {e} h => (authorized_exact e).mp h))
    (using_receipt reverseReceipt (fun {e} h => (authorized_exact e).mpr h))

end Yulang.GeneralDeclarativeGuardCurrent330
