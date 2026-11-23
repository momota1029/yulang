import Yulang.GeneralDeclarativeInspect321

namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeInspect321 (Visit Inspects)
open GeneralDeclarativeK2Graph321 (View)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem ordinary_walk_starts_with_inspection {view : View} {name site : Nat} {code : Expr}
    (visit : Visit view name code site) : Inspects code := by
  cases visit with
  | here head => exact head
  | primitive => exact .primitive
  | nominal => exact .nominal
  | field => exact .record
  | variant => exact .variant

theorem some_ordinary_visit_iff_inspects {view : View} {name : Nat} {code : Expr} :
    (∃ site, Visit view name code site) ↔ Inspects code :=
  ⟨fun ⟨_,walk⟩ => ordinary_walk_starts_with_inspection walk,fun h => ⟨name,.here h⟩⟩

end Yulang.GeneralDeclarativeI65
