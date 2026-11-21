import Yulang.GeneralMixedFullControlTrace306
import Yulang.GeneralMixedFullControlMinimal306

namespace Yulang.GeneralMixedFullControlScheduler306
open GeneralMixedFullControlCode306 (Code Event fire code)
open GeneralMixedControlLiveness306 (full)
open GeneralMixedControlMask306 (Mask rank)
open GeneralMixedFullControlTrace306 (check)
open GeneralMixedFullControlMinimal306 (obligations)

def terminal : Code := ⟨true,full⟩
def installCost (x : Code) : Nat := if x.installed then 0 else 1
def leastCost (x : Code) : Nat := installCost x + if x.scalars = full then 0 else 1

def finish (x : Code) : List (Event × Code) :=
  if x.installed then [] else [(.install,terminal)]

def fast (x : Code) : List (Event × Code) :=
  (if x.scalars = full then [] else
    [(.scalar (if x.scalars.zero then 1 else 0),⟨x.installed,full⟩)]) ++ finish x

def slow (x : Code) : List (Event × Code) :=
  (if x.scalars.zero then [] else [(.scalar 0,⟨x.installed,⟨true,x.scalars.one⟩⟩)]) ++
  (if x.scalars.one then [] else [(.scalar 1,⟨x.installed,full⟩)]) ++ finish x

theorem schedules (x : Code) :
    (check x terminal (fast x) = true ∧ (fast x).length = leastCost x) ∧
      (check x terminal (slow x) = true ∧ (slow x).length = obligations x) := by
  rcases x with ⟨a,⟨b,c⟩⟩
  cases a <;> cases b <;> cases c <;> decide

theorem single_bounds (e : Event) (x y : Code) (edge : fire e x y = true) :
    leastCost x ≤ leastCost y + 1 ∧ obligations y + 1 ≤ obligations x := by
  rcases x with ⟨a,⟨b,c⟩⟩
  rcases y with ⟨d,⟨f,g⟩⟩
  have sub i : (i : Fin 2) = 0 ∨ i = 1 := by
    have h : i.val = 0 ∨ i.val = 1 := by omega
    exact h.imp Fin.ext Fin.ext
  cases e with
  | install =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> cases g <;> revert edge <;> decide
  | scalar i =>
    rcases sub i with rfl|rfl <;>
      cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> cases g <;> revert edge <;> decide

theorem trace_bounds (x y : Code) (trace : List (Event × Code)) (run : check x y trace = true) :
    leastCost x ≤ trace.length + leastCost y ∧ trace.length + obligations y ≤ obligations x := by
  induction trace generalizing x with
  | nil =>
    have same : x = y := of_decide_eq_true run
    subst y
    simp
  | cons entry rest ih =>
    obtain ⟨e,next⟩ := entry
    obtain ⟨first,tailOK⟩ := Bool.and_eq_true_iff.mp run
    have start := single_bounds e x next first
    have stops := ih next tailOK
    simp only [List.length_cons]
    omega

theorem interval_width (x : Code) : obligations x ≤ leastCost x + 1 := by
  rcases x with ⟨a,⟨b,c⟩⟩
  cases a <;> cases b <;> cases c <;> decide

theorem exact_finishing_lengths (x : Code) (n : Nat) :
    (∃ trace : List (Event × Code), check x terminal trace = true ∧ trace.length = n) ↔
      leastCost x ≤ n ∧ n ≤ obligations x := by
  constructor
  · rintro ⟨trace,yes,rfl⟩
    have ok := trace_bounds x terminal trace yes
    have one : leastCost terminal = 0 := rfl
    have two : obligations terminal = 0 := rfl
    exact ⟨by simpa only [one,Nat.add_zero] using ok.1,by simpa only [two,Nat.add_zero] using ok.2⟩
  · rintro ⟨lo,hi⟩
    have width := interval_width x
    have endpoints : n = leastCost x ∨ n = obligations x := by omega
    rcases endpoints with rfl|rfl
    · exact ⟨fast x,(schedules x).1⟩
    · exact ⟨slow x,(schedules x).2⟩

end Yulang.GeneralMixedFullControlScheduler306
