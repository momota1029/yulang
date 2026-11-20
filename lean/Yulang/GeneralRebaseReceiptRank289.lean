import Yulang.GeneralRebaseReceiptRuntime289

/-! A decreasing rank for this fixed raw/sidecar product only. This is
not a rank for arbitrary raw journals or the general language resolver. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28800
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptRank289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptRawProduct289 (Config Next initial)
open GeneralRebaseReceiptMachine289 (Phase weight tick)
open GeneralRebaseReceiptScopedTrace289 (Family closed)
open GeneralRebaseReceiptFixture289 (wire request)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)

def rank (s : Config) : Nat :=
  (if s.raw.effects.isEmpty then 3 else 0) + weight s.phase

theorem decreases (choice : Bool) {x y : Config}
    (family : Family choice x) (edge : Next choice x y) : rank y < rank x := by
  cases edge with
  | side s p q took =>
    change _ + weight q < _ + weight p
    exact Nat.add_lt_add_left (GeneralRebaseReceiptMachine289.decreases _ _ _ _ took) _
  | raw s t p old =>
    cases family with
    | start =>
      rw [GeneralRebaseRowActualPaths287.only_before choice t old]
      show 2 < 5
      decide
    | earlyDenied =>
      rw [GeneralRebaseRowActualPaths287.only_before choice t old]
      show 2 < 3
      decide
    | afterScan => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
    | received _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
    | published _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
    | stillPending _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim

theorem accessible (choice : Bool) (s : Config) (family : Family choice s) :
    Acc (fun next current => Next choice current next) s := by
  have prove (n : Nat) : ∀ s, Family choice s → rank s = n →
      Acc (fun next current => Next choice current next) s := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s family rankEq
      constructor
      intro t edge
      have lower := decreases choice family edge
      rw [rankEq] at lower
      exact ih (rank t) lower t (closed choice family edge) rfl
  exact prove (rank s) s family rfl

end Yulang.GeneralRebaseReceiptRank289
