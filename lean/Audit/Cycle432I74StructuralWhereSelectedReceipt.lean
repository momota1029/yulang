import Yulang.GeneralDeclarativeI65I74StructuralWhereSelectedReceipt432
import Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2400
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociatedAudit432
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428 StructuralWhere431 WhereAssociated432
open StructuralWhereAuditFixture429 StructuralWhereReadback427

def wire : StructuralWhere431.Wire :=
  ⟨positiveWire,⟨parentEscape,nestedEscape⟩,⟨childEscape,scalarEscape⟩⟩
def packet : ActualPair fixture.state fixture.root :=
  (readOriginal fixture wire).get (by decide +kernel)

theorem true_original_structural_trace_locates_actual_selected_child432 :
    ∃ (t : CommonRoleOutermostResolver.Tree) (d : CommonRoleOutermostResolver.Dictionary) (e : Event fixture.state packet.pair.original.child)
        (source : SourceTrace R15.named426 fixture.state packet.pair.original.child t (some e)),
      ActualWhereTraceAt432 (actualSourceTrace431 packet) 0 source ∧
      [.node packet.pair.childFrame.decl.id []][0]? = some d ∧
      CommonRoleOutermostResolver.Summarizes t (.selected d) :=
  selected_parent_uses_actual_child_trace432 (actualSourceTrace431 packet)
    (exact_original_tree_summary431 packet)
    (by rw [(OriginalWhereFromSource431 packet).1]; rfl)

#print axioms actual_forest_trace_at_keeps_original_request432
#print axioms actual_where_trace_at_keeps_original_request432
#print axioms actual_selected_forest_at432
#print axioms selected_parent_uses_actual_child_trace432
#print axioms actual_where_child_supplies_original_lexical_output432
#print axioms true_original_structural_trace_locates_actual_selected_child432

end Yulang.GeneralDeclarativeI65.I72.WhereAssociatedAudit432
