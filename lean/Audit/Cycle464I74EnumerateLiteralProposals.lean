import Yulang.GeneralDeclarativeI65I74EnumerateLiteralProposals464

namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
#print axioms ordered_literal_proposals_iff_exact_actual_original_equations
#print axioms any_enumerated_proposal_already_carries_finite_equational_evidence
#print axioms enumeration_preserves_all_passed_old_ordinals_in_order

private def emp : Expr := .primitive .emptyRecord []
private def childForm : Expr := .record 40 (.variable 7) emp
private def parentForm : Expr := .record 30 childForm emp
private def old : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨4,parentForm⟩,⟨5,childForm⟩,⟨5,childForm⟩,⟨6,childForm⟩,⟨9,emp⟩]⟩

#guard ((allLiteralProposals old 0 [.recordPayload 30 emp]).map Prod.fst) == [1,2,3]
#guard (allLiteralProposals old 9 [.recordPayload 30 emp]).isEmpty
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
