import Yulang.GeneralRebaseMixedLength277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseBoundedInstallAcc277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseQuietBound277 (Counted)
open GeneralRebaseMixedCounts277 (Actual quietCap poly_mono sourceCap centerCap)
open GeneralRebaseMixedLength277 (actual_length)
variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {start : State roles}

theorem accessible_of_bound {α : Type} (step : α → α → Prop) (start : α) (limit : Nat)
    (every : ∀ n after, Counted step start n after → n ≤ limit) :
    Acc (fun after before => step before after) start := by
  have go : ∀ fuel n current, n + fuel = limit → Counted step start n current →
      Acc (fun after before => step before after) current := by
    intro fuel
    induction fuel with
    | zero =>
      intro n current used trace
      refine Acc.intro current ?_
      intro next edge
      have overshoot := every (n+1) next (.tail trace edge)
      omega
    | succ fuel ih =>
      intro n current used trace
      refine Acc.intro current ?_
      intro next edge
      exact ih (n+1) next (by omega) (.tail trace edge)
  exact go limit 0 start (Nat.zero_add _) .nil

theorem cap_mono (a b : Nat) (ordered : a ≤ b) : quietCap r start a ≤ quietCap r start b := by
  unfold quietCap sourceCap centerCap
  exact poly_mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ ordered) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ ordered) _)

theorem bounded_steps (initial : Reachable r root start) (K : Nat)
    (budget : ∀ n final, Counted (Actual r root) start n final →
      final.plans.length ≤ start.plans.length + K)
    (walk : Counted (Actual r root) start n after) :
    n ≤ K + (K+1) * quietCap r start K := by
  obtain ⟨k,recorded,upper⟩ := actual_length initial walk
  have kLe : k ≤ K := by have seen := budget n after walk; omega
  exact Nat.le_trans upper (Nat.add_le_add kLe (Nat.mul_le_mul (by omega) (cap_mono k K kLe)))

/-- A uniform bound on the actual installation ledger along finite prefixes
suffices for accessibility of the full mixed relation, without a separately
supplied rank on every state. Supplying such a bound is still a separate task. -/
theorem adapter_accessible (initial : Reachable r root start) (K : Nat)
    (budget : ∀ n final, Counted (Actual r root) start n final →
      final.plans.length ≤ start.plans.length + K) :
    Acc (fun after before => Actual r root before after) start :=
  accessible_of_bound (Actual r root) start (K + (K+1) * quietCap r start K)
    (fun _ _ walk => bounded_steps initial K budget walk)

end Yulang.GeneralRebaseBoundedInstallAcc277
