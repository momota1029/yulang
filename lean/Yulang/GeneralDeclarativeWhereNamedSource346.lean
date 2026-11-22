import Yulang.GeneralDeclarativeWhereNominalFixture346
import Yulang.GeneralDeclarativeInitialRoot343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeWhereNamedSource346
open GeneralDeclarativeInitialRoot343 (InputOrigin anchored support source_backed)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeOrigins321 (restriction backed_iff)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhereNominal346 (scan)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalCurrentRead319 (zero)
open GeneralNominalCommonBridge (Assignment)

/-- The fixture's actual raw current point-descriptor read and its
independent original source label select the *same literal* ordinary
row. Its support holds even when no output owner is completed, not
because the raw equation happened to be true. -/
theorem independent_at_actual_point (m : Assignment) (fit : GeneralWhereVersionInstall317.Models updated m) :
    scan GeneralWherePhysicalPast319.point 0 0 [2,2] = some zero ∧
    publicRow = (⟨0,.nominal 0 [.variable 2,.variable 2]⟩ : Equation) ∧
    InputOrigin publicRow ∧ publicRow ∈ (restriction (support (fun _ => False))).equations ∧
    Holds m publicRow := by
  refine ⟨GeneralDeclarativeWhereNominalFixture346.exact_current,rfl,anchored,
    (backed_iff _ _).mpr (source_backed _),?_⟩
  exact GeneralDeclarativeWhereNominalFixture346.actual_source m fit

end Yulang.GeneralDeclarativeWhereNamedSource346
