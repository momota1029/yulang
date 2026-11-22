import Yulang.GeneralDeclarativeOpenReadiness339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpenUnresolved339
open GeneralDeclarativeCompoundOpenFixture338
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem only_head {code : Expr} (there : (⟨0,code⟩ : Equation) ∈ (restriction p).equations) :
    code = raw := by
  have ordinary := originally there
  change (⟨0,code⟩ : Equation) ∈ [lhs,rhs,scalar] at ordinary
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ordinary
  rcases ordinary with yes|no|no
  · exact congrArg Equation.right yes
  · cases no
  · cases no

theorem not_inline {rs : List (Nat × Expr)} {term : Expr}
    (ending : Terminal term) (shape : withTail rs term = raw) : False := by
  cases rs with
  | nil => cases ending <;> cases shape
  | cons h front =>
    obtain ⟨k,v⟩ := h
    have merged := Expr.record.inj shape
    cases front with
    | nil =>
      exact (by
        have last := merged.2.2
        cases last
        cases ending)
    | cons next later =>
      obtain ⟨tag,payload⟩ := next
      have impossible := merged.2.2
      cases impossible

theorem prefixed_tail {rs : List (Nat × Expr)} {tail : Nat}
    (shape : withTail rs (.variable tail) = raw) : tail = 4 := by
  cases rs with
  | nil => cases shape
  | cons h front =>
    obtain ⟨k,v⟩ := h
    have merged := Expr.record.inj shape
    cases front with
    | nil => exact Expr.variable.inj merged.2.2
    | cons next later =>
      obtain ⟨tag,payload⟩ := next
      have impossible := merged.2.2
      cases impossible

/-- Stronger than the missing tail row alone: none of the real
authorized prefix paths can produce a settled C336 record Read at
the actual lower endpoint in this fixture. The earlier positive
legacy election remains distinct from this stronger proof boundary. -/
theorem no_settled_spine (seen : Spine (restriction p) 0 ls ending) : False := by
  cases seen with
  | width linked stored =>
    have eq := alias_only_self linked
    have impossible := only_head (eq.symm ▸ stored)
    cases impossible
  | exactEnd linked stored =>
    have eq := alias_only_self linked
    have impossible := only_head (eq.symm ▸ stored)
    cases impossible
  | cons linked stored tail =>
    have eq := alias_only_self linked
    have actual := only_head (eq.symm ▸ stored)
    have fix := Expr.variable.inj (Expr.record.inj actual).2.2
    exact tail_not_closed (.name (fix ▸ tail))
  | inline linked terminal stored =>
    have eq := alias_only_self linked
    exact not_inline terminal (only_head (eq.symm ▸ stored))
  | prefixed linked stored tail =>
    have eq := alias_only_self linked
    have fix := prefixed_tail (only_head (eq.symm ▸ stored))
    exact tail_not_closed (.name (fix ▸ tail))

theorem not_settled_read (seen : GeneralDeclarativeEndpointRecord336.Read p a keys ls us first last le ue) : False :=
  no_settled_spine seen.lo

end Yulang.GeneralDeclarativeOpenUnresolved339
