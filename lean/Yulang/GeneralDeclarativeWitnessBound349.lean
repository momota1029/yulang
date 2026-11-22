import Yulang.GeneralDeclarativeWitnessLiteral349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessBound349
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

inductive Path where
  | refl (atName : Nat)
  | interval (index : Nat)
  | constraint (index : Nat)
  | compose (first last : Path)

structure Checked (s : State) where
  lower : Nat
  upper : Nat
  fact : Bound s.normal lower upper

/-- The indexed table is the exact current, solver-free state.
A numeric proof node cannot instruct us to add a row. -/
def replay (s : State) : Path → Option (Checked s)
  | .refl n => some ⟨n,n,.refl n⟩
  | .interval ix =>
    match h : s.normal.intervals[ix]? with
    | none => none
    | some (a,b) => some ⟨a,b,.interval (List.mem_iff_getElem?.mpr ⟨ix,h⟩)⟩
  | .constraint ix =>
    match h : s.normal.ordinary[ix]? with
    | some (.tyLe (.var a) (.var b)) => some ⟨a,b,.constraint (List.mem_iff_getElem?.mpr ⟨ix,h⟩)⟩
    | _ => none
  | .compose x y => do
    let l ← replay s x
    let r ← replay s y
    if h : l.upper = r.lower
      then some ⟨l.lower,r.upper,.trans l.fact (h.symm ▸ r.fact)⟩
      else none

def check (s : State) (a b : Nat) (p : Path) : Bool :=
  ((replay s p).map (fun x => decide (x.lower = a ∧ x.upper = b))).getD false

theorem sound {s : State} {a b : Nat} {p : Path} (h : check s a b p = true) :
    Bound s.normal a b := by
  unfold check at h
  cases run : replay s p with
  | none => simp [run] at h
  | some x =>
    rw [run] at h
    change decide (x.lower = a ∧ x.upper = b) = true at h
    have equal := of_decide_eq_true h
    exact equal.1 ▸ equal.2 ▸ x.fact

structure Range where
  lowerToCenter : Path
  centerToUpper : Path

def fits (s : State) (arg : Capture) (c : Range) : Bool :=
  check s arg.lower arg.center c.lowerToCenter && check s arg.center arg.upper c.centerToUpper

theorem bounds_sound {s : State} {arg : Capture} {c : Range} (h : fits s arg c = true) :
    Bounds s arg :=
  ⟨sound (splitAnd h).1,sound (splitAnd h).2⟩

structure Shared where
  there : Path
  back : Path

def tied (s : State) (a b : Nat) (c : Shared) : Bool :=
  check s a b c.there && check s b a c.back

theorem alias_sound {s : State} {a b : Nat} {c : Shared} (h : tied s a b c = true) :
    Alias s a b :=
  .bounds (sound (splitAnd h).1) (sound (splitAnd h).2)

end Yulang.GeneralDeclarativeWitnessBound349
