import Yulang.GeneralDeclarativeWitnessOrigins350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNoHead350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias Knows constructorTag)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support visible visible_iff)
open GeneralDeclarativeWitnessRank350 (rank atom)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def equalOnFlat (levels : List Nat) (e : Equation) : Bool :=
  match e.right with
  | .variable b => decide (rank levels e.left = rank levels b)
  | _ => true

def outside (levels : List Nat) (root : Nat) (e : Equation) : Bool :=
  match constructorTag e.right with
  | none => true
  | some _ => decide (rank levels root ≠ rank levels e.left)

/-- The levels only separate an alias class; there is no structural
decrease premise here. The graph may have a real ordinary K2 cycle. -/
def check (s : State) (t : Table) (root : Nat) (levels : List Nat) : Bool :=
  ((s.normal.ordinary.all (atom (rank levels)) &&
    s.normal.intervals.all (fun e => decide (rank levels e.1 ≤ rank levels e.2))) &&
   (visible t).all (equalOnFlat levels)) &&
  (visible t).all (outside levels root)

theorem all_bounds {s : State} {ls : List Nat}
    (ordinary : s.normal.ordinary.all (atom (rank ls)) = true)
    (intervals : s.normal.intervals.all (fun e => decide (rank ls e.1 ≤ rank ls e.2)) = true)
    (path : Bound s.normal x y) : rank ls x ≤ rank ls y := by
  induction path with
  | interval h => exact of_decide_eq_true (List.all_eq_true.mp intervals _ h)
  | constraint h => exact of_decide_eq_true (List.all_eq_true.mp ordinary _ h)
  | refl _ => exact Nat.le_refl _
  | trans _ _ l r => exact Nat.le_trans l r

theorem alias_level {s : State} {t : Table} {a : Attached s t} {root : Nat} {ls : List Nat}
    (ok : check s t root ls = true) (edge : Alias (restriction (support a)) x y) :
    rank ls x = rank ls y := by
  have top := (splitAnd (splitAnd ok).1)
  have bounds := splitAnd top.1
  have flats := top.2
  induction edge with
  | bounds l r => exact Nat.le_antisymm (all_bounds bounds.1 bounds.2 l) (all_bounds bounds.1 bounds.2 r)
  | forward h => exact of_decide_eq_true (List.all_eq_true.mp flats _ ((visible_iff a _).mp h))
  | backward h =>
    apply Eq.symm
    exact of_decide_eq_true (List.all_eq_true.mp flats _ ((visible_iff a _).mp h))
  | trans _ _ l r => exact l.trans r

theorem unseen {s : State} {t : Table} {a : Attached s t} {root : Nat} {ls : List Nat}
    (ok : check s t root ls = true) : ∀ tag, ¬Knows (restriction (support a)) root tag := by
  intro tStore known
  obtain ⟨e,current,aliased,shape⟩ := known
  have extra := List.all_eq_true.mp (splitAnd ok).2 e ((visible_iff a _).mp current)
  unfold outside at extra
  rw [shape] at extra
  exact (of_decide_eq_true extra) (alias_level ok aliased)

end Yulang.GeneralDeclarativeWitnessNoHead350
