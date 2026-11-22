import Yulang.GeneralDeclarativeVersionedRetarget342
import Yulang.GeneralDeclarativeSubstitution320
import Yulang.GeneralWhereOriginDelta318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeVersionedRows342
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralNominalVersionedExpressionFrame236 (variableSource variable_value)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (environment variables_eq)
open GeneralRebaseRetarget275 (retarget Observed)
open GeneralNominalRefinements (Refines)
open GeneralWhereVersionCompiler317 (schema)

def names (p : Plan roles) (n : Nat) : Capture :=
  ⟨variableSource p .lower n,variableSource p .actual n,variableSource p .upper n⟩

def ordinary (p : Plan roles) (e : Equation) : GeneralDeclarativeHead320.Equation :=
  ⟨e.target,logical (names p) e.mode e.expression⟩

theorem variables_known (p : Plan roles) (m : Assignment) :
    variables (names p) m = GeneralNominalVersionedPlans231.variables p m := by
  funext mode name
  rw [variables_eq,variable_value]
  cases mode <;> rfl

/-- Lower and upper modes read exactly the compiler's physical
operands, while nested nominal parameters read actual operands.
No type equivalence substitutes a new output target. -/
theorem exact (p : Plan roles) (e : Equation) (m : Assignment) :
    GeneralDeclarativeEntailment320.Holds m (ordinary p e) ↔
     e.Holds (GeneralNominalVersionedPlans231.variables p m) m := by
  change CommonNominalFullCarrier.Equivalent (m e.target).1
    (value (environment m) .actual (logical (names p) e.mode e.expression)) ↔ _
  rw [logical_value,variables_known]
  rfl

theorem all (p : Plan roles) (m : Assignment)
    (known : GeneralWhereVersionSemantics317.Holds p m) :
    ∀ row ∈ (schema p).equations.map (ordinary p), GeneralDeclarativeEntailment320.Holds m row := by
  intro row there
  obtain ⟨e,printed,rfl⟩ := List.mem_map.mp there
  exact (exact p e m).mpr (known.rows e printed)

theorem aligned {p q : Plan roles} (same : GeneralNominalCenteredHeadMatPlanData.Same p q) :
    (schema p).equations.map (ordinary p) = (schema q).equations.map (ordinary q) := by
  have nameEq : names p = names q := by
    funext n
    unfold names
    rw [GeneralWhereVersionRecompile317.variable_eq same .lower n,
      GeneralWhereVersionRecompile317.variable_eq same .actual n,
      GeneralWhereVersionRecompile317.variable_eq same .upper n]
  rw [GeneralWhereVersionRecompile317.schema_eq same]
  apply List.map_congr_left
  intro row _
  unfold ordinary
  rw [nameEq]

theorem fixed (p : Plan roles) :
    ((schema p).equations.map (ordinary p)).map GeneralDeclarativeHead320.Equation.left =
    (schema p).equations.map Equation.target := by
  simp only [List.map_map]
  rfl

end Yulang.GeneralDeclarativeVersionedRows342
