import Yulang.GeneralDeclarativeAuthorizedCopy326
import Yulang.GeneralDeclarativeGraphFootprint326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCopyCollapse326
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAuthorizedCopy326 (name writing extended)
open GeneralDeclarativeFootprint321 (stateNames equationNames atomSources typeSources)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeNewNames321 (before_after)
open GeneralDeclarativeTraceNames321 (names)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def collapse (s : State) (source : Nat) (keep : List Nat) (n : Nat) :=
  if n = name s source keep then source else n

theorem base_unchanged {s : State} (source : Nat) (keep : List Nat)
    (old : n ∈ stateNames s) : collapse s source keep n = n := by
  have right : n < name s source keep := before_after
    (List.mem_append_left _ (List.mem_append_left _ old))
  simp [collapse,Nat.ne_of_lt right]

theorem chosen_unchanged (s : State) (source : Nat) (keep : List Nat) :
    collapse s source keep source = source := by
  simp [collapse]

theorem copy_collapses (s : State) (source : Nat) (keep : List Nat) :
    collapse s source keep (name s source keep) = source := by simp [collapse]

theorem ordinary_eq_names {s : State} (row : Equation) (listed : row ∈ s.equations) :
    equationNames row ⊆ stateNames s := by
  intro n used
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨row,listed,used⟩)

theorem bound {s : State} (source : Nat) (keep : List Nat) (known : Bound s.normal a b) :
    Bound s.normal (collapse s source keep a) (collapse s source keep b) := by
  induction known with
  | refl n => exact .refl _
  | @interval a b valid =>
    have both n (h : n ∈ ([a,b] : List Nat)) : n ∈ stateNames s :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a,b),valid,h⟩))
    rw [base_unchanged source keep (both a List.mem_cons_self),
      base_unchanged source keep (both b (List.mem_cons_of_mem _ List.mem_cons_self))]
    exact .interval valid
  | @constraint a b fact =>
    have both n (h : n ∈ ([a,b] : List Nat)) : n ∈ stateNames s :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,fact,h⟩))
    rw [base_unchanged source keep (both a List.mem_cons_self),
      base_unchanged source keep (both b (List.mem_cons_of_mem _ List.mem_cons_self))]
    exact .constraint fact
  | trans first next ih jh => exact .trans ih jh

theorem alias {s : State} (source : Nat) (keep : List Nat)
    (known : Alias (extended s source keep) a b) :
    Alias s (collapse s source keep a) (collapse s source keep b) := by
  have fromRow {a b : Nat} (written : (⟨a,.variable b⟩ : Equation) ∈ (extended s source keep).equations) :
      Alias s (collapse s source keep a) (collapse s source keep b) := by
    rcases List.mem_append.mp written with before|added
    · have keys := ordinary_eq_names _ before
      rw [base_unchanged source keep (keys List.mem_cons_self),
        base_unchanged source keep (keys (List.mem_cons_of_mem _ List.mem_cons_self))]
      exact .forward before
    · have same := List.mem_singleton.mp added
      have left : a = name s source keep := congrArg Equation.left same
      have right : b = source := by
        have h : Expr.variable b = Expr.variable source := congrArg Equation.right same
        exact Expr.variable.inj h
      rw [left,right,copy_collapses,chosen_unchanged]
      exact alias_refl _
  induction known with
  | bounds lower upper => exact .bounds (bound source keep lower) (bound source keep upper)
  | forward row => exact fromRow row
  | backward row => exact GeneralDeclarativeLowerKnown321.alias_symm (fromRow row)
  | trans _ _ ih jh => exact .trans ih jh

end Yulang.GeneralDeclarativeCopyCollapse326
