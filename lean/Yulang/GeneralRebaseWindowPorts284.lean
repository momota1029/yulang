import Yulang.GeneralRebaseWindowMinimum284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWindowPorts284
open GeneralRebaseRoundMicro278 (Tick Phase next)
open GeneralRebaseEpochWindow284 (Window view advance latestWritten previousKnown)
open GeneralRebaseInstallTimeline278 (installedCount)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)

inductive End where
  | lower | upper
  deriving DecidableEq, Repr
inductive Age where
  | previous | latest
  deriving DecidableEq, Repr
structure Port where
  age : Age
  side : End
  deriving DecidableEq, Repr

def admits (w : Window) : Age → Bool
  | .previous => previousKnown w
  | .latest => latestWritten w

def rootName (upper : Nat) : End → Nat
  | .lower => 2
  | .upper => upper

def read (upper : Nat) (w : Window) (p : Port) : Option Nat :=
  if admits w p.age then some (rootName upper p.side) else none

def rawIndex (t : Tick) : Age → Nat
  | .previous => t.round - 1
  | .latest => t.round

def rawAddr (lo hi : Nat → Nat) (t : Tick) (p : Port) : Nat :=
  match p.side with
  | .lower => lo (rawIndex t p.age + 1)
  | .upper => hi (rawIndex t p.age)

def present (t : Tick) : Age → Prop
  | .previous => 0 < t.round
  | .latest => t.round < installedCount t

theorem presence (t : Tick) (age : Age) : admits (view t) age = true ↔ present t age := by
  cases age
  · rcases t with ⟨n,p⟩
    cases n <;> simp [admits,previousKnown,view,present]
  · exact GeneralRebaseEpochWindow284.written t

theorem exact_reads (upper : Nat) (t : Tick) (p : Port) (source : Nat) :
    read upper (view t) p = some source ↔ present t p.age ∧ source = rootName upper p.side := by
  unfold read
  by_cases enabled : admits (view t) p.age = true
  · rw [ite_eq_left enabled]
    simp only [Option.some.injEq,(presence t p.age).mp enabled,true_and,eq_comm]
  · rw [ite_eq_right enabled]
    have impossible : ¬ present t p.age := fun yes => enabled ((presence t p.age).mpr yes)
    simp [impossible]

theorem previous_has_index (t : Tick) (age : Age) (active : present t age) :
    rawIndex t age < installedCount t := by
  rcases t with ⟨n,p⟩
  cases age
  · cases p <;> simp [present,rawIndex,installedCount] at active ⊢ <;> omega
  · exact active

theorem carry (later : Bool) (upper : Nat) (side : End) :
    read upper (advance ⟨later,.refreshed⟩) ⟨.previous,side⟩ =
      read upper ⟨later,.refreshed⟩ ⟨.latest,side⟩ := rfl

theorem carry_raw (lo hi : Nat → Nat) (n : Nat) (side : End) :
    rawAddr lo hi (next ⟨n,.refreshed⟩) ⟨.previous,side⟩ =
      rawAddr lo hi ⟨n,.refreshed⟩ ⟨.latest,side⟩ := by
  cases side <;> rfl

theorem root_bound (upper : Nat) (w : Window) (p : Port) (k : Nat)
    (seen : read upper w p = some k) : k ∈ [2,upper] := by
  unfold read at seen
  split at seen
  · have eq := Option.some.inj seen
    subst k
    cases p.side <;> simp [rootName]
  · cases seen

end Yulang.GeneralRebaseWindowPorts284
