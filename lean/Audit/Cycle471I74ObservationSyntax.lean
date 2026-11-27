import Yulang.GeneralDeclarativeI65I74ObservationSyntax471

namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471.Audit
open GeneralNominalCenteredHeadMatExpressions (Expr)
private def empty : Expr := .primitive .emptyRecord []
private def literal : Expr := .record 40 (.variable 1)
  (.record 30 (.variant 18 (.variable 2)) (.record 40 (.variable 9) empty))

theorem sorting_does_not_select_shadowed_payloads (s : GeneralDeclarativeI65.State) :
    readDescription s literal =
      some (.structural (.record [30,40]),[(.field 30,.variant 18 (.variable 2)),(.field 40,.variable 1)]) := by
  simp [literal,empty,readDescription,literalFields,sortedFields,CommonRoleCanonicalRows.normalize,
    CommonRoleCanonicalRows.residual]

theorem open_tail_and_join_are_not_observed_constructors (s : GeneralDeclarativeI65.State) :
    readDescription s (.record 40 (.variable 1) (.variable 2)) = none ∧
    readDescription s (.join literal literal) = none := ⟨rfl,rfl⟩

#print axioms description_exact
#print axioms sorted_fields_keep_exact_first_visible_entries
#print axioms sorted_labels_are_canonical
#print axioms sorting_does_not_select_shadowed_payloads
#print axioms open_tail_and_join_are_not_observed_constructors
end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471.Audit
