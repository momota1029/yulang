import Yulang.GeneralRebaseWatchValidator284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchBudgetProbe284
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseWatchValidator284 (Compact Valid update high admits checkRows)
open GeneralRebaseFutureWatch284 (Closed Covers)
open GeneralRebaseWatchStep284 (next NoReveal)
open GeneralPresenceOrderedBlock247 (solve SafeOrder)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

/-- Synthetic family: every new definition reads only stable source 1. The
indexed stream is a representation probe, not a Yulang source trace. -/
def cell (n : Nat) : Entry Nat := (n+2,.var 1)
def saved (n : Nat) : Compact := ⟨n+2,[1,n+2],[cell n]⟩
def journal : Nat → List (Entry Nat)
  | 0 => [cell 0]
  | n+1 => cell (n+1) :: journal n

theorem compact_step (n : Nat) :
    update (saved n) (saved (n+1)).watch [cell (n+1)] = some (saved (n+1)) := by
  have lower : n+1+2 > n+2 := by omega
  have notLower : ¬ n+1<n := by omega
  have notOne (m : Nat) : m+2 ≠ 1 := by omega
  simp [update,saved,cell,next,GeneralRebaseFutureWatch284.trim,GeneralRebaseSortedCache283.push,
    GeneralRebaseSortedCache283.insert,admits,checkRows,GeneralPresenceUsedSupport245.typedReads,
    high,lower,notLower,notOne,Nat.max_eq_right (Nat.le_of_lt lower)]

theorem coherent (n : Nat) : GeneralNominalAcyclicEquations237.Coherent (journal n) := by
  have shape (e : Entry Nat) (used : e ∈ journal n) : e.2 = .var 1 := by
    induction n with
    | zero =>
      rcases List.mem_singleton.mp used with rfl
      rfl
    | succ n ih =>
      rcases List.mem_cons.mp used with rfl|rest
      · rfl
      · exact ih rest
  exact fun a ha b hb _ => (shape a ha).trans (shape b hb).symm

theorem initial : Valid (saved 0) (journal 0) := by
  refine ⟨?_,⟨?_,fun {_} h => h,fun _ h _ => h⟩,?_⟩
  · intro e used; cases List.mem_singleton.mp used; decide
  · intro e used _
    cases List.mem_singleton.mp used
    intro id present
    have eq : id = 1 := List.mem_singleton.mp present
    subst id
    exact List.mem_cons_self
  · exact List.pairwise_singleton _ _

theorem correct (n : Nat) : Valid (saved n) (journal n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    have parts (e : Entry Nat) : e ∈ journal (n+1) ↔ e ∈ [cell (n+1)] ∨ e ∈ journal n := by
      simp [journal]
    exact (GeneralRebaseWatchValidator284.checked ih parts (coherent (n+1)) (compact_step n)).1

theorem size_contrast (n : Nat) : (saved n).kept.length = 1 ∧ (journal n).length = n+1 := by
  constructor
  · rfl
  · induction n with
    | zero => rfl
    | succ n ih => simp [journal,ih]

def hole : Compact := ⟨8,[1],[]⟩
theorem conservative : update hole [1,2] [] = none := rfl
theorem gap_safe : NoReveal [1] [1,2] [(8,.var 1)] := by
  intro row used picked
  cases List.mem_singleton.mp used
  simp at picked

end Yulang.GeneralRebaseWatchBudgetProbe284
