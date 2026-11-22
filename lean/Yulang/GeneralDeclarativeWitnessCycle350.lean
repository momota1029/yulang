import Yulang.GeneralDeclarativeWitnessRank350
import Yulang.GeneralDeclarativeWitnessBound349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCycle350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeWitnessBound349 (Shared tied alias_sound)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativePriority321 (RootRecurs)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

inductive Link where
  | same
  | bounds (proof : Shared)
  | forward (row : Nat)
  | backward (row : Nat)
  | compose (middle : Nat) (first last : Link)

def checksLink (s : State) (x y : Nat) : Link → Bool
  | .same => decide (x = y)
  | .bounds w => tied s x y w
  | .forward i => decide (s.equations[i]? = some ⟨x,.variable y⟩)
  | .backward i => decide (s.equations[i]? = some ⟨y,.variable x⟩)
  | .compose mid left right => checksLink s x mid left && checksLink s mid y right

theorem link {s : State} {x y : Nat} {w : Link} (ok : checksLink s x y w = true) : Alias s x y := by
  induction w generalizing x y with
  | same => cases of_decide_eq_true ok; exact alias_refl _
  | bounds => exact alias_sound ok
  | forward ix => exact .forward (List.mem_iff_getElem?.mpr ⟨ix,of_decide_eq_true ok⟩)
  | backward ix => exact .backward (List.mem_iff_getElem?.mpr ⟨ix,of_decide_eq_true ok⟩)
  | compose mid _ _ left right =>
    obtain ⟨a,b⟩ := splitAnd ok
    exact .trans (left a) (right b)

structure Hop where
  rowIndex : Nat
  linkOwner : Link
  child : Nat

def checksHop (s : State) (x : Nat) (w : Hop) : Bool :=
  match s.equations[w.rowIndex]? with
  | none => false
  | some row =>
    match shapeOf row.right with
    | none => false
    | some node => checksLink s x row.left w.linkOwner && decide (w.child ∈ node.children)

theorem hop {s : State} {x : Nat} {w : Hop} (ok : checksHop s x w = true) :
    Descends (structural s) x w.child := by
  unfold checksHop at ok
  cases found : s.equations[w.rowIndex]? with
  | none => simp [found] at ok
  | some e =>
    cases decoded : shapeOf e.right with
    | none => simp [found,decoded] at ok
    | some shape =>
      rw [found] at ok
      change (match shapeOf e.right with
        | none => false
        | some node => checksLink s x e.left w.linkOwner && decide (w.child ∈ node.children)) = true at ok
      rw [decoded] at ok
      obtain ⟨alias,child⟩ := splitAnd ok
      have raw : (⟨e.left,e.right⟩ : Equation) ∈ s.equations := by
        cases e
        exact List.mem_iff_getElem?.mpr ⟨w.rowIndex,found⟩
      exact ⟨shape,⟨e.left,link alias,e.right,raw,decoded⟩,of_decide_eq_true child⟩

def close (s : State) (x root : Nat) (last : Link) : List Hop → Bool
  | [] => checksLink s x root last
  | first :: next => checksHop s x first && close s first.child root last next

theorem path {s : State} {x root : Nat} {last : Link} {body : List Hop}
    (ok : close s x root last body = true) :
    ∃ endAt, Path (structural s) x endAt ∧ Alias s endAt root := by
  induction body generalizing x with
  | nil => exact ⟨x,.refl x,link ok⟩
  | cons first tail ih =>
    obtain ⟨here,rest⟩ := splitAnd ok
    obtain ⟨endAt,edges,alias⟩ := ih rest
    exact ⟨endAt,.next (hop here) edges,alias⟩

structure Wire where
  argument : Nat
  first : Hop
  rest : List Hop
  closeAt : Link

def check (s : State) (d : Demand) (w : Wire) : Bool :=
  match d.arguments[w.argument]? with
  | none => false
  | some a => checksHop s a.lower w.first && close s w.first.child a.lower w.closeAt w.rest

/-- Nonempty ordinary structural descent, closed back to the exact demanded
root. Mere alias reflexivity and an unreachable cyclic descendant are not
witnesses. This proves the root cycle only, not a language verdict. -/
theorem rooted {s : State} {d : Demand} {w : Wire} (ok : check s d w = true) : RootRecurs s d := by
  unfold check at ok
  cases found : d.arguments[w.argument]? with
  | none => simp [found] at ok
  | some a =>
    rw [found] at ok
    obtain ⟨step,tail⟩ := splitAnd ok
    obtain ⟨last,walk,l⟩ := path tail
    exact ⟨a,List.mem_iff_getElem?.mpr ⟨w.argument,found⟩,w.first.child,last,hop step,walk,l⟩

theorem no_positive {s : State} {d : Demand} {w : Wire} {levels}
    (ok : check s d w = true) (ranked : GeneralDeclarativeWitnessRank350.check s levels = true) : False := by
  obtain ⟨a,_,cycle⟩ := rooted ok
  exact GeneralDeclarativeTaggedElection340.no_cycles (GeneralDeclarativeWitnessRank350.sound ranked) a.lower cycle

end Yulang.GeneralDeclarativeWitnessCycle350
