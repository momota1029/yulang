import Yulang.GeneralDeclarativeTaggedElection340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRank350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeBounds319 (Bound)
open PresenceNormalForm (Atom)

abbrev Table := List Nat

def rank (levels : Table) (x : Nat) : Nat := levels[x]?.getD 0

def atom (r : Nat → Nat) : Atom Nat → Bool
  | .tyLe (.var a) (.var b) => decide (r a ≤ r b)
  | _ => true

def row (r : Nat → Nat) (e : Equation) : Bool :=
  match e.right with
  | .variable b => decide (r e.left = r b)
  | rhs => (names rhs).all (fun n => decide (r n < r e.left))

/-- Check all generator edges of Bound, all flat aliases, and all
compound dependencies, even equations with no backing support. -/
def check (s : State) (levels : Table) : Bool :=
  (s.normal.ordinary.all (atom (rank levels)) &&
   s.normal.intervals.all (fun edge => decide (rank levels edge.1 ≤ rank levels edge.2))) &&
  s.equations.all (row (rank levels))

theorem sound {s : State} {levels : Table} (ok : check s levels = true) :
    Ranked s (rank levels) := by
  obtain ⟨ab,rows⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨ats,ints⟩ := Bool.and_eq_true_iff.mp ab
  constructor
  · intro a b proof
    induction proof with
    | interval used => exact of_decide_eq_true (List.all_eq_true.mp ints _ used)
    | constraint used => exact of_decide_eq_true (List.all_eq_true.mp ats _ used)
    | refl n => exact Nat.le_refl _
    | trans _ _ l h => exact Nat.le_trans l h
  · intro a b used
    exact of_decide_eq_true (List.all_eq_true.mp rows _ used)
  · intro e used n needs notVariable
    have verified := List.all_eq_true.mp rows e used
    cases h : e.right with
    | «variable» b => exact False.elim (notVariable b h)
    | primitive | nominal | record | variant | join =>
      unfold row at verified
      rw [h] at verified needs
      exact of_decide_eq_true (List.all_eq_true.mp verified _ needs)

theorem safe {s : State} {levels : Table} (ok : check s levels = true) :
    ¬ GeneralDeclarativePriority321.Recurs s r i tests d :=
  GeneralDeclarativeTaggedElection340.safe (sound ok)

end Yulang.GeneralDeclarativeWitnessRank350
