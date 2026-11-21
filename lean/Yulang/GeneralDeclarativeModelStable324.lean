import Yulang.GeneralDeclarativeRuleExact323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeModelStable324
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Entails Holds appendFacts model_append conservative_append)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarations (Checked)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeRuleExact323 (exact)
open GeneralDeclarativeRigidLocal323 (RootClosed)

def StableUnder (s : State) (applies : Equation → Prop) : Prop :=
  ∀ row, applies row → ∀ m, Models s m → Models (appendFacts s [row]) m

/-- Closure is stated by the independent, ordinary one-rule update.
It does not assert anything about whether a candidate was selected. -/
theorem stable_exact {s : State} {applies : Equation → Prop} :
    StableUnder s applies ↔ ∀ row, applies row → Entails s row := by
  constructor
  · intro stable row source m valid
    exact ((model_append m).mp (stable row source m valid)).2 row List.mem_cons_self
  · intro ordinary row source m valid
    exact (conservative_append (fun e h => (List.mem_singleton.mp h).symm ▸ ordinary row source) m).mpr valid

theorem stable_batch {s : State} {applies : Equation → Prop}
    (stable : StableUnder s applies) (justified : ∀ row ∈ rows, applies row) (m) :
    Models (appendFacts s rows) m ↔ Models s m :=
  conservative_append (fun row found => stable_exact.mp stable row (justified row found)) m

/-- Only the given parsed rule instances need be covered. Other rules
can still refine this state; this is not a claim of global saturation. -/
theorem closes_root {s : State} (checked : Checked r) (cover : Coverage r interp)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (stable : StableUnder s applies)
    (enabled : ∀ row, SourceEquation r interp d impl capture row → applies row) :
    RootClosed s r interp d impl capture :=
  (exact checked cover visible role wanted).mpr (fun row source => stable_exact.mp stable row (enabled row source))

theorem appended_stable (s : State) (rows : List Equation) :
    StableUnder (appendFacts s rows) (fun e => e ∈ rows) := by
  apply stable_exact.mpr
  intro row inRows
  exact GeneralDeclarativeEntailment320.literal (List.mem_append_right _ inRows)

end Yulang.GeneralDeclarativeModelStable324
