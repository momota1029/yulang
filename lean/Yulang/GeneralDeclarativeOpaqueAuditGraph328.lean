import Yulang.GeneralDeclarativeOpaqueCompress328
import Yulang.GeneralDeclarativeGraphFootprint326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueAuditGraph328
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOpaqueIntervals328 (Ends protect left right ready)
open GeneralDeclarativeOpaqueNames328 (kept first second row)
open GeneralDeclarativeOpaqueCompress328 (small squash old_name keeps left_center right_center project_alias)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeCopyCollapse326 (ordinary_eq_names)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeGraphFootprint326 (shape_children)
open GeneralDeclarativeK2Graph321 (View Descends Path aliasView Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)

/-- Finite graph abstraction for diagnostics only. A virtual pair uses
old lower names, never claims they denote the actual center. -/
def upperView (s : State) (root : Nat) (e : Ends) : View := fun n head =>
  observed s n head ∨ n = root ∧ head = .primitive .pair [e.firstLo,e.secondLo]

section
variable (s : State) (root : Nat) (keep : List Nat) (e : Ends)
local notation "q" => squash s root keep e
local notation "R" => (ready s root keep e)
local notation "V" => (upperView s root e)
local notation "C" => (small s e)

theorem root_fixed : q root = root :=
  keeps s root keep e (List.mem_append_right _ List.mem_cons_self)

theorem direct {a b : Nat} (step : Descends (observed R) a b) :
    Descends V (q a) (q b) := by
  obtain ⟨head,⟨exp,present,printed⟩,member⟩ := step
  rcases List.mem_append.mp present with old|new
  · have footprint := ordinary_eq_names ⟨a,exp⟩ old
    rw [old_name s root keep e (footprint List.mem_cons_self),
      old_name s root keep e (footprint (List.mem_cons_of_mem _ (shape_children printed member)))]
    exact ⟨head,.inl ⟨exp,old,printed⟩,member⟩
  · have eq := List.mem_singleton.mp new
    have source : a = root := congrArg Equation.left eq
    have code : exp = (row s root (protect keep e)).right := congrArg Equation.right eq
    subst a
    rw [code] at printed
    cases printed
    rw [root_fixed]
    refine ⟨_,.inr ⟨rfl,rfl⟩,?_⟩
    change b ∈ [first s root (protect keep e),second s root (protect keep e)] at member
    change q b ∈ [e.firstLo,e.secondLo]
    rcases List.mem_cons.mp member with left|right
    · rw [left,left_center]
      exact List.mem_cons_self
    · rw [List.mem_singleton.mp right,right_center]
      exact List.mem_cons_of_mem _ List.mem_cons_self

theorem edge {a b : Nat} (step : Descends (aliasView R (observed R)) a b) :
    Descends (aliasView C V) (q a) (q b) := by
  obtain ⟨head,⟨w,linked,found⟩,member⟩ := step
  obtain ⟨tag,source,part⟩ := direct s root keep e ⟨head,found,member⟩
  exact ⟨tag,⟨q w,project_alias s root keep e linked,source⟩,part⟩

theorem path {a b : Nat} (moves : Path (aliasView R (observed R)) a b) :
    Path (aliasView C V) (q a) (q b) := by
  induction moves with
  | refl => exact .refl _
  | next step _ rest => exact .next (edge s root keep e step) rest

/-- No-cycle checking can use an over-approximation on old names plus
two endpoint bridges. The opposite direction is not claimed, as a
fresh child need not actually alias the lower endpoint it maps to. -/
theorem cycle {n : Nat} (loops : AliasCycle R (observed R) n) :
    AliasCycle C V (q n) := by
  obtain ⟨child,last,first,rest,returns⟩ := loops
  exact ⟨q child,q last,edge s root keep e first,path s root keep e rest,
    project_alias s root keep e returns⟩

theorem no_cycle {n : Nat} (safe : ¬ AliasCycle C V (q n)) :
    ¬ AliasCycle R (observed R) n :=
  fun loops => safe (cycle s root keep e loops)

end
end Yulang.GeneralDeclarativeOpaqueAuditGraph328
