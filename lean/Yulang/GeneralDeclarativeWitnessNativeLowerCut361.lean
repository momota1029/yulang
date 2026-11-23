import Yulang.GeneralDeclarativeWitnessSequentialReceiver361
import Yulang.GeneralDeclarativeLowerKnown321
import Yulang.GeneralDeclarativeWitnessRank350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 56000000
namespace Yulang.GeneralDeclarativeWitnessNativeLowerCut361
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias Knows Delayed)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessSequentialReceiver361 (Received receive)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessNativeInstall360 (atTarget)
open GeneralDeclarativeWitnessNativeSnapshot360 (same_exact)
open PresenceNormalForm (Atom)

def atom (mark : Nat → Bool) : Atom Nat → Bool
  | .tyLe (.var a) (.var b) => decide (mark a = mark b)
  | _ => true

def row (mark : Nat → Bool) (e : Equation) : Bool :=
  match e.right with
  | .variable v => decide (mark e.left = mark v)
  | rhs => if (GeneralDeclarativeLowerKnown321.constructorTag rhs).isSome then !mark e.left else true

/-- A decidable barrier for ordinary lower knowledge. This checks even
unbacked constraints, so it cannot be made to pass by hiding ordinary rows. -/
def check (s : State) (mark : Nat → Bool) : Bool :=
  (s.normal.ordinary.all (atom mark) &&
    s.normal.intervals.all (fun (a,b) => decide (mark a = mark b))) &&
    s.equations.all (row mark)

theorem bound_keeps {s : State} {mark : Nat → Bool} (checked : check s mark = true)
    (b : Bound s.normal n k) : mark n = mark k := by
  have tests := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1)
  induction b with
  | interval edge => exact of_decide_eq_true (List.all_eq_true.mp tests.2 _ edge)
  | constraint edge => exact of_decide_eq_true (List.all_eq_true.mp tests.1 _ edge)
  | refl _ => rfl
  | trans _ _ ih jh => exact ih.trans jh

theorem alias_keeps {s : State} {mark : Nat → Bool} (checked : check s mark = true)
    (a : Alias s n k) : mark n = mark k := by
  have rows := (Bool.and_eq_true_iff.mp checked).2
  induction a with
  | bounds l _ => exact bound_keeps checked l
  | forward e => exact of_decide_eq_true (List.all_eq_true.mp rows _ e)
  | backward e => exact (of_decide_eq_true (show decide (mark _ = mark _) = true from
      List.all_eq_true.mp rows _ e)).symm
  | trans _ _ ih jh => exact ih.trans jh

theorem row_outside {mark : Nat → Bool} {e : Equation} (ok : row mark e = true)
    (h : GeneralDeclarativeLowerKnown321.constructorTag e.right = some tag) : mark e.left = false := by
  cases hR : e.right with
  | «variable» n => rw [hR] at h; cases h
  | join a b => rw [hR] at h; cases h
  | primitive | nominal | record | variant =>
    unfold row at ok
    rw [hR] at ok
    simpa [GeneralDeclarativeLowerKnown321.constructorTag] using ok

theorem no_constructor {s : State} {mark : Nat → Bool} (checked : check s mark = true)
    (inside : mark n = true) (known : Knows s n tag) : False := by
  obtain ⟨e,present,same,shape⟩ := known
  have ok := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 _ present
  exact Bool.noConfusion (inside.symm.trans ((alias_keeps checked same).trans (row_outside ok shape)))

theorem no_backed_constructor {s : State} {mark : Nat → Bool} {done} (p : Supported s done)
    (checked : check s mark = true) (inside : mark n = true) :
    ¬Knows (restriction p) n tag := by
  intro known
  refine no_constructor checked inside (GeneralDeclarativeLowerKnown321.knows_mono (s := restriction p) (t := s) rfl ?_ known)
  intro e included
  obtain ⟨o,why,_⟩ := (GeneralDeclarativeOrigins321.backed_iff p e).mp included
  exact p.ordinary why

def component (n : Nat) : Bool := [101,112,113,116,117].contains n

theorem exact_cut : check GeneralDeclarativeWitnessSequentialNative360.final component = true ∧
    check GeneralDeclarativeWitnessSequentialReceiver361.finalState component = true := by decide +kernel

def sequenceFootprint {negative r} (s : @Sequence negative r) : Bool :=
  check s.final.ordinary component &&
    (decide (s.place.lower = 112 ∧ s.place.center = 101 ∧ s.place.upper = 113)) &&
    (atTarget s.final.board s.place.lower).isNone

theorem actual_cut (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map sequenceFootprint).getD false = true := by
  cases negative <;> decide +kernel

theorem checked_body_is_not_ordinary_ready {negative} {r : Run negative} {s : Sequence r}
    (root : originalBody negative = some r) (sent : sequence r = some s) {done}
    (p : Supported s.final.ordinary done) :
    Delayed p s.receiver ∧ atTarget s.final.board s.place.lower = none := by
  have proof := actual_cut negative
  rw [root] at proof
  change ((sequence r).map sequenceFootprint).getD false = true at proof
  rw [sent] at proof
  have fact := Bool.and_eq_true_iff.mp (show sequenceFootprint s = true from proof)
  have shape := Bool.and_eq_true_iff.mp fact.1
  have literal := of_decide_eq_true shape.2
  refine ⟨⟨s.place,?_,fun _ => no_backed_constructor p shape.1 ?_⟩,?_⟩
  · rw [s.args]; exact List.mem_cons_self
  · rw [literal.1]; rfl
  · exact Option.isNone_iff_eq_none.mp fact.2


def levels : List Nat := [0,0,0,0] ++ List.replicate 114 1

theorem rank_exact :
    GeneralDeclarativeWitnessRank350.check GeneralDeclarativeWitnessSequentialNative360.final levels = true ∧
    GeneralDeclarativeWitnessRank350.check GeneralDeclarativeWitnessSequentialReceiver361.finalState levels = true := by
  decide +kernel

def rankBefore {negative r} (s : @Sequence negative r) : Bool :=
  GeneralDeclarativeWitnessRank350.check s.final.ordinary levels

theorem actual_rank (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map rankBefore).getD false = true := by
  cases negative <;> decide +kernel

theorem checked_body_is_not_an_ordinary_K2_rejection {negative} {r : Run negative} {s : Sequence r}
    (root : originalBody negative = some r) (sent : sequence r = some s) {registry interp tests} :
    ¬ GeneralDeclarativePriority321.Recurs s.final.ordinary registry interp tests s.receiver := by
  have h := actual_rank negative
  rw [root] at h
  change ((sequence r).map rankBefore).getD false = true at h
  rw [sent] at h
  exact GeneralDeclarativeWitnessRank350.safe (show rankBefore s = true from h)

theorem ordinary_projection_is_pending_not_selected {negative} {r : Run negative} {s : Sequence r}
    (root : originalBody negative = some r) (sent : sequence r = some s) {done}
    (p : Supported s.final.ordinary done) {registry interp tests generates} :
    GeneralDeclarativePriority321.Local s.final.ordinary registry interp p tests generates s.receiver .pending ∧
    ∀ result, GeneralDeclarativePriority321.Local s.final.ordinary registry interp p tests generates s.receiver result →
      result = .pending := by
  have delayed := (checked_body_is_not_ordinary_ready root sent p).1
  have safe := checked_body_is_not_an_ordinary_K2_rejection root sent
    (registry := registry) (interp := interp) (tests := tests)
  exact ⟨.unsupported delayed safe,fun _ => GeneralDeclarativePriority321.delayed_pending_only delayed⟩

end Yulang.GeneralDeclarativeWitnessNativeLowerCut361
