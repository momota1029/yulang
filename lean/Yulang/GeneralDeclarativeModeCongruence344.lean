import Yulang.GeneralDeclarativeCommitPosition344
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

namespace Yulang.GeneralDeclarativeModeCongruence344
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (nominal_congr primitive_congr)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalVersionedExpressionFrame236 (reads readsMany)
open GeneralNominalMaterialization (Mode)
open GeneralNominalMatchedAssembly (Aligned)

mutual
theorem expression (first last : Mode → Nat → Ty) (mode : Mode) (code : Expr)
    (same : ∀ key ∈ reads mode code, Equivalent (first key.1 key.2) (last key.1 key.2)) :
    Equivalent (value first mode code) (value last mode code) := by
  cases code with
  | «variable» name => exact same (mode,name) List.mem_cons_self
  | primitive ctor args => exact primitive_congr ctor (expressions first last mode args same)
  | nominal name args => exact nominal_congr name (expressions first last .actual args same)
  | record label a b =>
    exact record_congr label
      (expression first last mode a (fun k h => same k (List.mem_append_left _ h)))
      (expression first last mode b (fun k h => same k (List.mem_append_right _ h)))
  | variant tag a => exact variant_congr tag (expression first last mode a same)
  | join a b =>
    exact union_congr
      (expression first last mode a (fun k h => same k (List.mem_append_left _ h)))
      (expression first last mode b (fun k h => same k (List.mem_append_right _ h)))

theorem expressions (first last : Mode → Nat → Ty) (mode : Mode) (codes : List Expr)
    (same : ∀ key ∈ readsMany mode codes, Equivalent (first key.1 key.2) (last key.1 key.2)) :
    Aligned Equivalent (values first mode codes) (values last mode codes) := by
  cases codes with
  | nil => exact .nil
  | cons a rest =>
    exact .cons (expression first last mode a (fun k h => same k (List.mem_append_left _ h)))
      (expressions first last mode rest (fun k h => same k (List.mem_append_right _ h)))
end

end Yulang.GeneralDeclarativeModeCongruence344
