import Yulang.GeneralRebaseReceiptControls289

/-! Pure sidecar transitions. The stamp carries a finite Offer only; a
publication always rechecks it against the current Wire. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReceiptMachine289
open GeneralRebaseReceiptWire289

inductive Stop where
  | denied (why : Decision)
  | stale
  deriving Repr, DecidableEq

inductive Phase where
  | scan
  | received (stamp : Offer)
  | published (stamp : Offer)
  | stopped (why : Stop)
  deriving Repr, DecidableEq

def tick (w : Wire) (ask : Offer) : Phase → Option Phase
  | .scan =>
    match check w ask with
    | .ready => some (.received ask)
    | failure => some (.stopped (.denied failure))
  | .received stamp =>
    if stamp = ask then
      match check w ask with
      | .ready => some (.published stamp)
      | failure => some (.stopped (.denied failure))
    else some (.stopped .stale)
  | .published _ | .stopped _ => none

def weight : Phase → Nat
  | .scan => 2
  | .received _ => 1
  | .published _ | .stopped _ => 0

theorem received_exact (w : Wire) (ask key : Offer) (p : Phase) :
    tick w ask p = some (.received key) ↔ p = .scan ∧ key = ask ∧ check w ask = .ready := by
  cases p <;> cases checked : check w ask <;> simp [tick,checked,eq_comm]
  all_goals split <;> simp_all [eq_comm]

theorem published_exact (w : Wire) (ask key : Offer) (p : Phase) :
    tick w ask p = some (.published key) ↔ p = .received ask ∧ key = ask ∧ check w ask = .ready := by
  cases p <;> cases checked : check w ask <;> simp [tick,checked,eq_comm]
  all_goals split <;> simp_all [eq_comm]

theorem decreases (w : Wire) (ask : Offer) (before after : Phase)
    (moved : tick w ask before = some after) : weight after < weight before := by
  cases before <;> cases checked : check w ask <;> simp [tick,checked] at moved
  all_goals first
    | (subst after; simp [weight])
    | (split at moved <;> simp_all only [Option.some.injEq] <;> subst after <;> simp [weight])

def advance (w : Wire) (ask : Offer) (p : Phase) : Phase := (tick w ask p).getD p

def run (w : Wire) (ask : Offer) : Phase :=
  advance w ask (advance w ask .scan)

theorem run_ready (w : Wire) (ask : Offer) (ready : check w ask = .ready) :
    run w ask = .published ask := by simp [run,advance,tick,ready]

theorem run_denial (w : Wire) (ask : Offer) (failure : check w ask ≠ .ready) :
    run w ask = .stopped (.denied (check w ask)) := by
  cases tested : check w ask <;> simp_all [run,advance,tick]

theorem run_terminal (w : Wire) (ask : Offer) : tick w ask (run w ask) = none := by
  by_cases ready : check w ask = .ready
  · rw [run_ready w ask ready]
    rfl
  · rw [run_denial w ask ready]
    rfl

theorem stale_stops (w : Wire) (old ask : Offer) (different : old ≠ ask) :
    tick w ask (.received old) = some (.stopped .stale) := by
  simp [tick,different]

end Yulang.GeneralRebaseReceiptMachine289
