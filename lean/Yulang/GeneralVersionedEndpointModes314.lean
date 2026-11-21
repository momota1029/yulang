import Yulang.GeneralVersionedRevisitEndpoints314

set_option backward.isDefEq.respectTransparency false
/-! An endpoint expression needs equality up to semantic equivalence only
at its actual mode-sensitive reads. Nominal subexpressions use actual values
even in a lower/upper row. These are exact expressions of the materializer. -/
namespace Yulang.GeneralVersionedEndpointModes314
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalVersionedExpressionFrame236 (reads readsMany)
open GeneralDictionaryDefaultExpression209 (primitive_equivalent nominal_equivalent)
open CommonNominalFullCarrier
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralFiniteTypedWrites312 (transitive)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCenters (Plan)

mutual
 theorem value_agrees (mode : Mode) (expr : Expr)
    (same : ∀ cell ∈ reads mode expr, Equivalent (first cell.1 cell.2) (last cell.1 cell.2)) :
    Equivalent (value first mode expr) (value last mode expr) := by
  cases expr with
  | «variable» n => exact same (mode,n) (List.mem_singleton_self _)
  | primitive constructor args => exact primitive_equivalent constructor (values_agree mode args same)
  | nominal n args => exact nominal_equivalent n (values_agree .actual args same)
  | record label a b =>
    exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr label
      (value_agrees mode a (fun name found => same name (List.mem_append_left _ found)))
      (value_agrees mode b (fun name found => same name (List.mem_append_right _ found)))
  | variant tag a =>
    exact GeneralNominalCenteredHeadMatPatternSemantics.variant_congr tag (value_agrees mode a same)
  | join a b =>
    exact GeneralNominalCenteredHeadMatPatternSemantics.union_congr
      (value_agrees mode a (fun name found => same name (List.mem_append_left _ found)))
      (value_agrees mode b (fun name found => same name (List.mem_append_right _ found)))
 theorem values_agree (mode : Mode) (xs : List Expr)
    (same : ∀ cell ∈ readsMany mode xs, Equivalent (first cell.1 cell.2) (last cell.1 cell.2)) :
    All₂ Equivalent (values first mode xs) (values last mode xs) := by
  cases xs with
  | nil => exact .nil
  | cons a rest =>
    exact .cons
      (value_agrees mode a (fun name found => same name (List.mem_append_left _ found)))
      (values_agree mode rest (fun name found => same name (List.mem_append_right _ found)))
end

theorem reuse_exact {p q : Plan roles} {m : Assignment} {row : Equation}
    (written : row.Holds (variables q m) m)
    (same : ∀ cell ∈ reads row.mode row.expression,
      Equivalent (variables q m cell.1 cell.2) (variables p m cell.1 cell.2)) :
    row.Holds (variables p m) m :=
  transitive written (value_agrees _ _ same)

end Yulang.GeneralVersionedEndpointModes314
