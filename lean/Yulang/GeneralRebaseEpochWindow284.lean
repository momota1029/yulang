import Yulang.GeneralRebaseVersionErasureFailure284
import Yulang.GeneralRebaseLooseErasureFailure284
import Yulang.GeneralRebaseVersionKnown278
import Yulang.GeneralRebaseLooseKnown278
import Yulang.GeneralRebaseVersionAbsorb278
import Yulang.GeneralRebaseLooseAbsorb278

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseEpochWindow284
open GeneralRebaseRoundMicro278 (Tick Phase next iterate)
open GeneralRebaseInstallTimeline278 (installedCount observedCount)

structure Window where
  later : Bool
  phase : Phase
  deriving DecidableEq, Repr

def table : List Window :=
  [⟨false,.enter⟩,⟨false,.installed⟩,⟨false,.refreshed⟩,
   ⟨true,.enter⟩,⟨true,.installed⟩,⟨true,.refreshed⟩]

theorem table_complete (w : Window) : w ∈ table := by
  rcases w with ⟨bit,p⟩
  cases bit <;> cases p <;> decide

theorem table_size : table.length = 6 := rfl
theorem table_distinct : table.Nodup := by decide

def view (t : Tick) : Window := ⟨t.round != 0,t.phase⟩

def advance (s : Window) : Window :=
  match s.phase with
  | .enter => ⟨s.later,.installed⟩
  | .installed => ⟨s.later,.refreshed⟩
  | .refreshed => ⟨true,.enter⟩

theorem forward (t : Tick) : view (next t) = advance (view t) := by
  rcases t with ⟨n,p⟩
  cases p <;> rfl

def start : Window := ⟨false,.enter⟩
def run : Nat → Window
  | 0 => start
  | n+1 => advance (run n)

theorem exact_run (n : Nat) : run n = view (iterate n) := by
  induction n with
  | zero => rfl
  | succ n ih => unfold run iterate; rw [ih,forward]

def canInstall (w : Window) : Bool := w.phase == .enter
def latestKnown (w : Window) : Bool := w.phase == .refreshed
def previousKnown (w : Window) : Bool := w.later
def latestWritten (w : Window) : Bool := w.phase != .enter

theorem ready_iff (t : Tick) : canInstall (view t) = true ↔ t.phase = .enter := by
  rcases t with ⟨n,p⟩; cases p <;> simp [canInstall,view]

theorem fresh_observed (t : Tick) : latestKnown (view t) = true ↔ t.round < observedCount t := by
  rcases t with ⟨n,p⟩; cases p <;> simp [latestKnown,view,observedCount]

theorem prior_observed (t : Tick) :
    previousKnown (view t) = true ↔ ∃ index, index+1 = t.round ∧ index < observedCount t := by
  rcases t with ⟨n,p⟩
  cases n with
  | zero => simp [previousKnown,view]
  | succ n =>
    cases p <;> simp [previousKnown,view,observedCount] <;> omega

theorem written (t : Tick) : latestWritten (view t) = true ↔ t.round < installedCount t := by
  rcases t with ⟨n,p⟩; cases p <;> simp [latestWritten,view,installedCount]

theorem cycle (later : Bool) :
    advance (advance (advance ⟨later,.enter⟩)) = ⟨true,.enter⟩ := rfl

theorem no_acc : ¬ Acc (fun next old => next = advance old) start := by
  have impossible (w : Window) (accessible : Acc (fun next old => next = advance old) w) : False := by
    induction accessible with
    | intro state take ih => exact ih (advance state) rfl
  exact impossible start

end Yulang.GeneralRebaseEpochWindow284
