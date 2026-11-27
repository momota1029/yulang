import Yulang.GeneralDeclarativeI65I74PreparedTableExact463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarations (Declaration)

/-- GD checks a declaration for an authored registry, not for a request or
a raw constraint graph. Re-indexing the same checked rows requires exact
registry equality, and executes no certificate verifier. -/
def reindexCheckedTable {before after : Current} (authority : authoredRegistry before = authoredRegistry after)
    (table : CheckedTable before) : CheckedTable after :=
  ⟨table.rows,fun d seen => authority ▸ table.prepared d seen⟩

theorem no_rechecking_for_the_same_actual_authored_registry
    {before after : Current} (authority : authoredRegistry before = authoredRegistry after)
    (t : CheckedTable before) (d : Declaration) :
    tableContains (reindexCheckedTable authority t) d = tableContains t d := rfl

theorem exact_registry_reindexing_preserves_stored_declaration_order
    {before after : Current} (authority : authoredRegistry before = authoredRegistry after)
    (t : CheckedTable before) :
    (reindexCheckedTable authority t).rows = t.rows := rfl

theorem reindexing_to_exact_original_registry_keeps_the_whole_table
    {before after : Current} (authority : authoredRegistry before = authoredRegistry after)
    (t : CheckedTable before) :
    reindexCheckedTable authority.symm (reindexCheckedTable authority t) = t := by
  cases t
  rfl

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
