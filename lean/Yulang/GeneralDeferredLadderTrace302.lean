import Yulang.GeneralDeferredLadderExact302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderTrace302
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderAdvance302 (run phase_step)
open GeneralDeferredLadderExact302 (Promotion RawStep only_step install_not_promotion)
open GeneralObservedLadderRefresh301 (before)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)
open B4Target (Steps)

inductive InstallTrace (n : Nat) : Nat → State roles → State roles → Prop
  | zero (state) : InstallTrace n 0 state state
  | next : InstallTrace n count fromState state → RawStep state target → ¬ Promotion n state target →
      InstallTrace n (count+1) fromState target

theorem exact_prefix (n k : Nat) (cap : k ≤ n+1) {count : Nat} {s : State roles}
    (trace : InstallTrace n count (run n k cap).state s) :
    ∃ available : k+count ≤ n+1, s = (run n (k+count) available).state := by
  have gen {l : Nat} {a b : State roles} (path : InstallTrace n l a b) (starts : a = (run n k cap).state) :
      ∃ available : k+l ≤ n+1, b = (run n (k+l) available).state := by
    induction path with
    | zero => exact ⟨by omega,starts⟩
    | next _ step no ih =>
      obtain ⟨cap,rfl⟩ := ih starts
      rcases only_step n _ cap _ step with ⟨available,rfl⟩|promotion
      · exact ⟨by omega,rfl⟩
      · exact False.elim (no promotion)
  exact gen trace rfl

theorem prefix_exists (n k : Nat) (cap : k ≤ n+1) :
    InstallTrace n k (before n) (run n k cap).state := by
  induction k with
  | zero => exact .zero _
  | succ k ih => exact .next (ih (by omega)) (phase_step n k (by omega)) (install_not_promotion n k (by omega))

theorem ordinary_path {n count : Nat} {s t : State roles}
    (trace : InstallTrace n count s t) : Steps RawStep s t := by
  induction trace with
  | zero => exact .refl
  | next _ step _ ih => exact .tail ih step

theorem promotion_required_to_halt (n count : Nat) (s : State roles)
    (path : InstallTrace n count (before n) s) :
    ∃ t, RawStep s t ∧ Promotion n s t := by
  obtain ⟨available,rfl⟩ := exact_prefix n 0 (by omega) path
  let p := run n (0+count) available
  let t := GeneralDeferredLadderRefresh302.promoted p
  exact ⟨t,GeneralDeferredLadderRefresh302.actual p,
    ⟨_,GeneralDeferredLadderRefresh302.certificate p,GeneralDeferredLadderRefresh302.strict p,rfl⟩⟩

end Yulang.GeneralDeferredLadderTrace302
