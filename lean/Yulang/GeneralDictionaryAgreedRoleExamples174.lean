import Yulang.GeneralDictionaryAgreedEdge174
import Yulang.GeneralDeclarationExamples

/-! Nonleaf positive and same-role-recursive negative regression for the
role-DAG fragment. The negative example remains a valid checked declaration;
it is not rejected by the language. -/
namespace Yulang.GeneralDictionaryAgreedRoleExamples174
open GeneralDeclarations GeneralDeclarationExamples GeneralDictionaryAgreedEdge174
open GeneralNominalSupport GeneralSourceDictionaries GeneralNominalActualAgreedLocal
open CommonRoleOutermostResolver (Child)

abbrev wrapOnly : Registry := ⟨constructors,roles,[wrap]⟩
def roleRank (role : Nat) : Nat := if role = 1 then 1 else 0

theorem wrapOnly_checked : Checked wrapOnly := by
  refine ⟨by simp,?_⟩
  intro declaration member
  cases List.mem_singleton.mp member
  exact wrap_checked

theorem wrapOnly_nonleaf : wrap.requirements ≠ [] := by simp

theorem wrapOnly_stratified : RoleStratified wrapOnly roleRank := by
  intro declaration member clause present
  cases List.mem_singleton.mp member
  cases List.mem_singleton.mp present
  decide +kernel

theorem wrapOnly_accessible (defer : Bool) (gap : GapPredicate roles)
    (state : Tracked roles) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local
      (GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary wrapOnly state)) root :=
  boundary_whereAccessible wrapOnly_stratified root

theorem display_not_stratified (rank : Nat → Nat) : ¬ RoleStratified registry rank := by
  intro stratified
  have impossible := stratified display (by simp) displayChild (by simp)
  exact Nat.lt_irrefl _ impossible

end Yulang.GeneralDictionaryAgreedRoleExamples174
