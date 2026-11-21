import Yulang.GeneralDeclarativeRigidSource323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidOccurrences323
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralDeclarativeTermOccurrences322 (actual_positions source_binders)
open GeneralDeclarativeRepeatedActual323 (Rigid RigidMany)
open GeneralDeclarativeRigidSource323 (Scanned Ordered)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (normalize normalizeArgs variablesArgs)

theorem as_walk (read : Rigid mode actual expression seen) : Walk mode actual expression seen :=
  Rigid.rec
    (motive_1 := fun mode a e seen _ => Walk mode a e seen)
    (motive_2 := fun mode as es seen _ => WalkMany mode as es seen)
    Walk.capture
    (fun _ _ ih jh => .primitive (.cons ih (by simpa using WalkMany.cons jh WalkMany.nil)))
    (fun _ ih => .nominal ih)
    (.primitive .nil)
    .nil
    (fun _ _ ih jh => .cons ih jh)
    read

theorem scanned_occurrences {s : State} (view : Scanned s c interp arg p seen) :
    seen.map Occurrence.binder = (normalize p).variables ∧
      ∀ o ∈ seen, o.mode = .actual := by
  obtain ⟨term,raw,code,_,_,translated,walk⟩ := view.exact
  have a := as_walk walk
  exact ⟨(source_binders translated a).1,(actual_positions a).2⟩

theorem exact_occurrences {s : State} (views : Ordered s c interp args ps seen) :
    seen.map Occurrence.binder = variablesArgs (normalizeArgs ps) ∧
      ∀ o ∈ seen, o.mode = .actual := by
  induction views with
  | nil => exact ⟨rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons first _ ih =>
    have a := scanned_occurrences first
    exact ⟨by rw [List.map_append,a.1,ih.1]; rfl,
      fun o h => (List.mem_append.mp h).elim (a.2 o) (ih.2 o)⟩

end Yulang.GeneralDeclarativeRigidOccurrences323
