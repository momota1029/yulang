import Yulang.GeneralDeclarativeWitnessTree349
import Yulang.GeneralDeclarativeTaggedElection340
import Yulang.GeneralDeclarativeCurrentReceipt330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessGround349
open GeneralDeclarativeHead320 (State Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralCandidateInspection (Primitive)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeCurrentReceipt330 (Receipt literal)
open GeneralDeclarativeGrowth327 (Extends)

deriving instance DecidableEq for Primitive

def row (key : Nat) (kind : Primitive) : Equation := ⟨key,.primitive kind []⟩

def isRow (key : Nat) (kind : Primitive) (e : Equation) : Bool :=
  match e.right with
  | .primitive other [] => decide (key = e.left ∧ kind = other)
  | _ => false

theorem is_row {key : Nat} {kind : Primitive} {e : Equation} :
    isRow key kind e = true ↔ row key kind = e := by
  cases e with
  | mk key' rhs =>
    cases rhs
    case primitive actual args =>
      cases args
      · simp [isRow,row]
      · simp [isRow,row]
    all_goals simp [isRow,row]

def occurs (s : State) (key : Nat) (kind : Primitive) : Bool :=
  s.equations.any (isRow key kind)

theorem occurrence {s : State} {key : Nat} {kind : Primitive} :
    occurs s key kind = true ↔ row key kind ∈ s.equations := by
  rw [occurs,List.any_eq_true]
  constructor
  · rintro ⟨e,inList,same⟩
    exact (is_row.mp same).symm ▸ inList
  · intro used
    exact ⟨_,used,is_row.mpr rfl⟩

def noDeps (e : Equation) : Bool :=
  match e.right with
  | .variable _ => true
  | expr => (names expr).isEmpty

def safeRows (s : State) : Bool := s.equations.all noDeps

/-- A sufficient rank certificate, checked on all ordinary rows, not
on the authorized source subset. Failure is not a K2 diagnosis. -/
theorem ranked {s : State} (checked : safeRows s = true) : Ranked s (fun _ => 0) := by
  refine ⟨(fun _ => Nat.le_refl _),(fun _ => rfl),?_⟩
  intro e seen n used notVar
  have no := List.all_eq_true.mp checked e seen
  have empty : names e.right = [] := by
    cases eq : e.right
    case «variable» v => exact False.elim (notVar v eq)
    all_goals
      unfold noDeps at no
      rw [eq] at no
      exact List.isEmpty_iff.mp no
  rw [empty] at used
  cases used

def carries (s : State) (e : Equation) : Bool :=
  match e.right with
  | .primitive kind [] => occurs s e.left kind
  | _ => false

theorem carries_row {s : State} {e : Equation} (checked : carries s e = true) : e ∈ s.equations := by
  cases e with
  | mk key expr =>
    cases expr <;> try cases checked
    case primitive kind args =>
      cases args with
      | nil => exact occurrence.mp checked
      | cons _ _ => cases checked

/-- Exact literal receipt for the ground first fragment. It neither
adds equations to the ambient state nor evaluates them in a chosen model. -/
def receives (ordinary current : State) : Bool :=
  (ordinary.normal.ordinary.isEmpty && ordinary.normal.intervals.isEmpty) &&
    ordinary.equations.all (carries current)

theorem receipt {ordinary current : State} (ok : receives ordinary current = true) :
    Receipt ordinary current := by
  obtain ⟨lists,rows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ok
  obtain ⟨atoms,bounds⟩ := GeneralDeclarativeWitnessProblem349.splitAnd lists
  apply literal
  refine ⟨?_,?_,fun e used => carries_row (List.all_eq_true.mp rows e used)⟩
  · intro e used
    rw [List.isEmpty_iff.mp atoms] at used
    cases used
  · intro e used
    rw [List.isEmpty_iff.mp bounds] at used
    cases used

end Yulang.GeneralDeclarativeWitnessGround349
